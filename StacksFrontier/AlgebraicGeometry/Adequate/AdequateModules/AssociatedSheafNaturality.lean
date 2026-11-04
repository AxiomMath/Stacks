module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AssociatedModuleAdjunction
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.BaseFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModuleSheafification
public import StacksFrontier.AlgebraicGeometry.Descent.SectionsPullbackComparison.Comparison
public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleFunctor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The functor `u` of Tag 06VN computes the associated module, naturally in the module

Over a scheme `S` the functor `u : QCoh(𝒪_S) ⥤ Mod((Sch/S)_fppf, 𝒪)` of [Stacks, Tag 06VN] is
defined as the pullback of sheaves of modules along the morphism of ringed sites
`((Sch/S)_fppf, 𝒪) → (S_Zar, 𝒪_S)`, while the source's `𝓖ᵃ` of [Stacks, Tag 03DU] (3) is
defined by its sections, `𝓖ᵃ(T) = Γ(T, T.hom^*𝓖)`. The two agree, because the sections presheaf
is already a sheaf and the sheafification inside the pullback therefore does nothing; that
agreement is `Stacks.Adequate.BigSite.associatedModuleFunctorObjIso`, **one quasi-coherent
module at a time**.

This module upgrades it to an isomorphism of **functors**. That is what [Stacks, Tag 06ZR] needs:
its remaining input `hacyc` compares object properties of complexes, and transporting a condition
on a complex of `u𝓖ᵢ` to the same condition on the complex of the `𝓖ᵢᵃ` asks for an isomorphism
of complexes, hence for naturality in the module of the identification of the terms.

## Main definitions

* `Stacks.Adequate.pullbackSectionsSheafFunctor` — the sections description of `𝓖ᵃ` as a functor
  on the quasi-coherent `𝒪_S`-modules: `𝓖 ↦ (T ↦ Γ(T, T.hom^*𝓖))`, with the map induced by
  `φ : 𝓖 ⟶ 𝓗` given over each object of the site by `Γ(T, T.hom^*φ)`.
* `Stacks.Adequate.BigSite.associatedModuleQcohIsoSections` — **the identification of the two
  constructions, naturally in the quasi-coherent module.**

## Main results

* `Stacks.Adequate.sectionsUnit_naturality_module` — pulling a section of `𝓖` over an open `U`
  of `S` back to the open subscheme `U` is natural in `𝓖`. On components this is
  `AlgebraicGeometry.Scheme.Modules.pullbackSection_naturality`, and it is the one piece of
  genuine content: everything else is the category algebra of transposing it across two
  adjunctions.
* `Stacks.Adequate.sectionsComparison_naturality_module` — hence the comparison of
  [Stacks, Tag 070S] (1) is natural in the module, being that square transposed along
  `CategoryTheory.PresheafOfModules.pullbackPushforwardAdjunction`.
* `Stacks.Adequate.associatedModuleIsoSections_hom_naturality_module` and
  `Stacks.Adequate.associatedModuleIsoSectionsSheaf_hom_naturality_module` — hence
  [Stacks, Tag 070S] (1) itself is natural in the module, first with the sheafification in place
  and then with it stripped against the sheaf condition of [Stacks, Tag 03DT].
* `Stacks.Adequate.BigSite.pullbackSectionsSheafFunctor_obj_val_obj` — the sections of the
  right-hand side over an object of the site read off as `Γ(T, T.hom^*𝓖)`, by definitional
  unfolding. Its affine-section form, and the consequence for the remaining input of
  [Stacks, Tag 06ZR], are in
  `StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/DerivedLocalizationAffineSections.lean`.

## Implementation notes

**One spelling throughout.** The library has two spellings of the presheaf of pullback sections,
`AlgebraicGeometry.BigFppfOver.sectionsPresheafOfModules` and
`Stacks.Sites.associatedModulePresheaf`. They are equal by `rfl`, and at the level of *objects*
that `rfl` is cheap; at the level of *morphisms* it is far over the heartbeat budget, because the
two carry different named `Module` instances on their sections and `PresheafOfModules.Hom`
compares them. So every statement below stays in the first spelling, which is the one
[Stacks, Tag 070S] (1) is proved in; the crossing to the chosen big site's spelling is made once,
at the end, where only functors and objects are compared. `Stacks.Adequate`
`.pullbackSectionsSheafFunctor` is built by hand from
`Stacks.Adequate.pullbackSectionsSheafMap` for the same reason: taking it to be
`Stacks.Sites.associatedSheafFunctor` would put that morphism-level `rfl` into every naturality
square.

**Why the conjugation lemmas are abstract.** The right adjoint of
`CategoryTheory.PresheafOfModules.sheafification` is a composite of two functors, and the
naturality of the sheafification counit records its middle object in the composite spelling
while the isomorphism being post-composed records it in the applied one. The two are equal by
`rfl` but not at the transparency at which `rw` and `simp only` recheck a goal, so those tactics
fail on the assembled square. `Stacks.Adequate.counit_conjugate_algebra` states the category
algebra with every object and arrow abstract; applying it is a single `exact`, which unifies at
default transparency. This mirrors `AlgebraicGeometry.SmallEtale.unit_conjugate_algebra`, which
exists for the same reason on the small étale site.

## References

* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
* [Stacks Project, Tag 03FH](https://stacks.math.columbia.edu/tag/03FH)
* [Stacks Project, Tag 06VN](https://stacks.math.columbia.edu/tag/06VN)
* [Stacks Project, Tag 06ZR](https://stacks.math.columbia.edu/tag/06ZR)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite
open AlgebraicGeometry.BigFppfOver

universe u

namespace Stacks.Adequate

section Naturality

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The sections presheaf is functorial in the module -/

/-- **The presheaf of pullback sections of [Stacks, Tag 03DS] is functorial in the module.** A
morphism `φ : 𝓖 ⟶ 𝓗` of quasi-coherent `𝒪_S`-modules induces, over each object `T / S` of the
big fppf site, the map `Γ(T, T.hom^*𝓖) ⟶ Γ(T, T.hom^*𝓗)` on global sections of the pullbacks.

The underlying map of abelian presheaves is `Stacks.Sites.associatedPresheafMap`, i.e.
[Stacks, Tag 03DS] read as a functor in the module and restricted to the site; its linearity
over the global functions on each object is
`AlgebraicGeometry.Scheme.Modules.Hom.app_smul`. -/
public noncomputable def pullbackSectionsPresheafMap {F G : S.Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G) :
    sectionsPresheafOfModules B S hS F ⟶ sectionsPresheafOfModules B S hS G :=
  PresheafOfModules.homMk
    (Stacks.Sites.associatedPresheafMap S (Over.post (X := B.obj hS) B.inclusion) φ)
    fun _ r m => Scheme.Modules.Hom.app_smul _ r m

/-- **Pulling sections back is natural in the module.** The morphism
`AlgebraicGeometry.BigFppfOver.sectionsUnit`, which sends a section of `𝓖` over an open `U` of
`S` to its pullback to the open subscheme `U`, commutes with a morphism `φ : 𝓖 ⟶ 𝓗` of
quasi-coherent modules.

On components this is `AlgebraicGeometry.Scheme.Modules.pullbackSection_naturality`: the
pullback of `φ.app U a` is the image under the pullback of `φ` of the pullback of `a`. This is
the only content in the file; every statement below it is category algebra. -/
public theorem sectionsUnit_naturality_module {F G : S.Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G) :
    (SheafOfModules.forget S.ringCatSheaf).map φ ≫ sectionsUnit B S hS G =
      sectionsUnit B S hS F ≫ (PresheafOfModules.pushforward.{u}
        (structureMap B S hS).hom).map (pullbackSectionsPresheafMap B S hS φ) := by
  refine PresheafOfModules.Hom.ext ?_
  ext U a
  exact (Scheme.Modules.pullbackSection_naturality (Scheme.Opens.ι U.unop) φ U.unop ⊤
    (Scheme.Opens.top_le_ι_preimage le_rfl) a).symm

/-- **The comparison of [Stacks, Tag 070S] (1) is natural in the module.** For a morphism
`φ : 𝓖 ⟶ 𝓗` of quasi-coherent `𝒪_S`-modules, the presheaf-level pullback of `φ` followed by the
comparison at `𝓗` is the comparison at `𝓖` followed by the induced map of pullback-sections
presheaves.

`AlgebraicGeometry.BigFppfOver.sectionsComparison` is the transpose of
`AlgebraicGeometry.BigFppfOver.sectionsUnit` along
`CategoryTheory.PresheafOfModules.pullbackPushforwardAdjunction`, so this square is that of
`Stacks.Adequate.sectionsUnit_naturality_module` transposed: both
`CategoryTheory.Adjunction.homEquiv_naturality_left_symm` and
`CategoryTheory.Adjunction.homEquiv_naturality_right_symm` apply. -/
public theorem sectionsComparison_naturality_module {F G : S.Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G) :
    (PresheafOfModules.pullback.{u} (structureMap B S hS).hom).map
          ((SheafOfModules.forget S.ringCatSheaf).map φ) ≫
        sectionsComparison B S hS G =
      sectionsComparison B S hS F ≫ pullbackSectionsPresheafMap B S hS φ := by
  unfold sectionsComparison
  rw [← Adjunction.homEquiv_naturality_left_symm, ← Adjunction.homEquiv_naturality_right_symm,
    sectionsUnit_naturality_module]

/-- **[Stacks, Tag 070S] (1) is natural in the module.** For a morphism `φ : 𝓖 ⟶ 𝓗` of
quasi-coherent `𝒪_S`-modules the identification of `𝓖ᵃ` with the sheafification of the
pullback-sections presheaf carries `φᵃ` to the sheafification of the map of pullback-sections
presheaves induced by `φ`.

Two of the identification's factors supply this at once:
`AlgebraicGeometry.BigFppfOver.associatedModuleSheafificationIso` is an isomorphism of *functors*
on all `𝒪_S`-modules, so its naturality is available, and the remaining factor is
`CategoryTheory.PresheafOfModules.sheafification` applied to
`AlgebraicGeometry.BigFppfOver.sectionsComparison`, whose naturality in the module is
`Stacks.Adequate.sectionsComparison_naturality_module`. -/
public theorem associatedModuleIsoSections_hom_naturality_module {F G : S.Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G) :
    (associatedModule B S hS).map φ ≫ (associatedModuleIsoSections B S hS G).hom =
      (associatedModuleIsoSections B S hS F).hom ≫
        (PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf B S hS).obj)).map
          (pullbackSectionsPresheafMap B S hS φ) := by
  unfold associatedModuleIsoSections associatedModuleIsoSectionsSheafification
  simp only [Iso.trans_hom, Iso.app_hom, asIso_hom]
  have key :
      (PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf B S hS).obj)).map
            ((PresheafOfModules.pullback.{u} (structureMap B S hS).hom).map
              ((SheafOfModules.forget S.ringCatSheaf).map φ)) ≫
          (PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf B S hS).obj)).map
            (sectionsComparison B S hS G) =
        (PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf B S hS).obj)).map
            (sectionsComparison B S hS F) ≫
          (PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf B S hS).obj)).map
            (pullbackSectionsPresheafMap B S hS φ) := by
    rw [← Functor.map_comp, ← Functor.map_comp, sectionsComparison_naturality_module]
  rw [← Category.assoc, (associatedModuleSheafificationIso B S hS).hom.naturality φ]
  simp only [Category.assoc]
  exact congrArg (fun t => (associatedModuleSheafificationIso B S hS).hom.app F ≫ t) key

/-! ### Stripping the sheafification -/

/-- **The presheaf of pullback sections as a sheaf of modules on the big fppf site.** The sheaf
condition is [Stacks, Tag 03DT], which is
`AlgebraicGeometry.BigFppfOver.isSheaf_sectionsPresheafOfModules_baseOverTopology`; no
sheafification occurs. -/
public noncomputable def pullbackSectionsSheaf (F : S.Modules) [F.IsQuasicoherent] :
    SheafOfModules.{u} (structureSheaf B S hS) :=
  ⟨sectionsPresheafOfModules B S hS F,
    isSheaf_sectionsPresheafOfModules_baseOverTopology B S hS .fppf F⟩

/-- `Stacks.Adequate.pullbackSectionsPresheafMap` read as a morphism of sheaves of modules. -/
public noncomputable def pullbackSectionsSheafMap {F G : S.Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G) :
    pullbackSectionsSheaf B S hS F ⟶ pullbackSectionsSheaf B S hS G :=
  ⟨pullbackSectionsPresheafMap B S hS φ⟩

/-- **[Stacks, Tag 070S] (1) with the sheafification stripped.** The associated module `𝓖ᵃ` *is*
the sheaf of pullback sections: by [Stacks, Tag 070S] (1) it is the fppf sheafification of the
pullback-sections presheaf, and by [Stacks, Tag 03DT] that presheaf is already a sheaf, so the
sheafification is inverted by the counit of the sheafification adjunction. -/
public noncomputable def associatedModuleIsoSectionsSheaf (F : S.Modules) [F.IsQuasicoherent] :
    (associatedModule B S hS).obj F ≅ pullbackSectionsSheaf B S hS F :=
  associatedModuleIsoSections B S hS F ≪≫
    (asIso ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (structureSheaf B S hS).obj)).counit)).app (pullbackSectionsSheaf B S hS F)

/-- The forward map of `Stacks.Adequate.associatedModuleIsoSectionsSheaf`, named so that the
naturality proof can rewrite with it rather than unfold the composite; see the module
documentation for why unfolding it inside a tactic block does not work. -/
public theorem associatedModuleIsoSectionsSheaf_hom (F : S.Modules) [F.IsQuasicoherent] :
    (associatedModuleIsoSectionsSheaf B S hS F).hom =
      (associatedModuleIsoSections B S hS F).hom ≫
        ((PresheafOfModules.sheafificationAdjunction
          (𝟙 (structureSheaf B S hS).obj)).counit).app (pullbackSectionsSheaf B S hS F) := rfl

/-- The category algebra of post-composing a naturality square with a second naturality square,
with every object and arrow abstract.

Stating it abstractly keeps the application a single `exact`, which unifies at default
transparency: the right adjoint of `CategoryTheory.PresheafOfModules.sheafification` is a
composite of two functors, and the naturality of the sheafification counit records its middle
object in the composite spelling while the isomorphism post-composed here records it in the
applied one. -/
private theorem counit_conjugate_algebra {C : Type*} [Category* C] {O₁ O₂ O₃ O₄ O₅ O₆ : C}
    (m : O₁ ⟶ O₂) (aF : O₁ ⟶ O₃) (aG : O₂ ⟶ O₄) (sh : O₃ ⟶ O₄)
    (cF : O₃ ⟶ O₅) (cG : O₄ ⟶ O₆) (sg : O₅ ⟶ O₆)
    (h1 : m ≫ aG = aF ≫ sh) (h2 : sh ≫ cG = cF ≫ sg) :
    m ≫ aG ≫ cG = (aF ≫ cF) ≫ sg := by
  rw [← Category.assoc, h1, Category.assoc, h2, Category.assoc]

/-- **[Stacks, Tag 070S] (1) with the sheafification stripped is natural in the module.**
`Stacks.Adequate.associatedModuleIsoSectionsSheaf` post-composes
`Stacks.Adequate.associatedModuleIsoSections` with the sheafification counit at a presheaf which
is a sheaf; since the counit is a natural transformation, this preserves the naturality of
`Stacks.Adequate.associatedModuleIsoSections_hom_naturality_module`. -/
public theorem associatedModuleIsoSectionsSheaf_hom_naturality_module {F G : S.Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G) :
    (associatedModule B S hS).map φ ≫ (associatedModuleIsoSectionsSheaf B S hS G).hom =
      (associatedModuleIsoSectionsSheaf B S hS F).hom ≫ pullbackSectionsSheafMap B S hS φ := by
  rw [associatedModuleIsoSectionsSheaf_hom, associatedModuleIsoSectionsSheaf_hom]
  exact counit_conjugate_algebra _ _ _ _ _ _ _
    (associatedModuleIsoSections_hom_naturality_module B S hS φ)
    (((PresheafOfModules.sheafificationAdjunction
      (𝟙 (structureSheaf B S hS).obj)).counit).naturality (pullbackSectionsSheafMap B S hS φ))

/-! ### The sections description as a functor, and the natural isomorphism -/

/-- The map of pullback-sections sheaves induced by the identity is the identity: over each
object of the site it is the identity pullback map on sections. -/
public theorem pullbackSectionsSheafMap_id (F : S.Modules) [F.IsQuasicoherent] :
    pullbackSectionsSheafMap B S hS (𝟙 F) = 𝟙 (pullbackSectionsSheaf B S hS F) := by
  refine SheafOfModules.hom_ext ?_
  refine PresheafOfModules.Hom.ext ?_
  ext X x
  exact congrFun (congrArg (fun χ => ⇑(AddCommGrpCat.Hom.hom (Scheme.Modules.Hom.app χ ⊤)))
    ((Scheme.Modules.pullback ((Over.post (X := B.obj hS) B.inclusion).obj X.unop).hom).map_id F))
    x

/-- The map of pullback-sections sheaves induced by a composite is the composite of the induced
maps. -/
public theorem pullbackSectionsSheafMap_comp {F G H : S.Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent] [H.IsQuasicoherent] (φ : F ⟶ G) (ψ : G ⟶ H) :
    pullbackSectionsSheafMap B S hS (φ ≫ ψ) =
      pullbackSectionsSheafMap B S hS φ ≫ pullbackSectionsSheafMap B S hS ψ := by
  refine SheafOfModules.hom_ext ?_
  refine PresheafOfModules.Hom.ext ?_
  ext X x
  exact congrFun (congrArg (fun χ => ⇑(AddCommGrpCat.Hom.hom (Scheme.Modules.Hom.app χ ⊤)))
    ((Scheme.Modules.pullback
      ((Over.post (X := B.obj hS) B.inclusion).obj X.unop).hom).map_comp φ ψ)) x

/-- **The sections description of `𝓖ᵃ`, as a functor on the quasi-coherent `𝒪_S`-modules**:
`𝓖 ↦ (T ↦ Γ(T, T.hom^*𝓖))`, with `φ : 𝓖 ⟶ 𝓗` sent to `Γ(T, T.hom^*φ)` over each object of the
site. This is [Stacks, Tag 03DX]'s functor read through
`AlgebraicGeometry.BigFppfOver.sectionsPresheafOfModules`; see the module documentation for why
it is built here rather than taken to be `Stacks.Sites.associatedSheafFunctor`. -/
@[sga "3 I 4.6.1"]
public noncomputable def pullbackSectionsSheafFunctor :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ⥤
      SheafOfModules.{u} (structureSheaf B S hS) where
  obj F := @pullbackSectionsSheaf B S hS F.obj F.property
  map {F G} φ := @pullbackSectionsSheafMap B S hS F.obj G.obj F.property G.property φ.hom
  map_id F := @pullbackSectionsSheafMap_id B S hS F.obj F.property
  map_comp {F G H} φ ψ :=
    @pullbackSectionsSheafMap_comp B S hS F.obj G.obj H.obj F.property G.property H.property
      φ.hom ψ.hom

/-- **The functor `u` of [Stacks, Tag 06VN] is the sections construction `𝓖 ↦ 𝓖ᵃ` of
[Stacks, Tag 03DU] (3), naturally in the quasi-coherent module.** This is
`Stacks.Adequate.associatedModuleIsoSectionsSheaf` assembled over all quasi-coherent modules,
its naturality being
`Stacks.Adequate.associatedModuleIsoSectionsSheaf_hom_naturality_module`. -/
public noncomputable def associatedModuleQcohIsoSections :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).ι ⋙ associatedModule B S hS ≅
      pullbackSectionsSheafFunctor B S hS :=
  NatIso.ofComponents (fun F => @associatedModuleIsoSectionsSheaf B S hS F.obj F.property)
    (fun {F G} φ =>
      @associatedModuleIsoSectionsSheaf_hom_naturality_module B S hS F.obj G.obj
        F.property G.property φ.hom)

end Naturality

/-! ### The identification at a chosen big fppf site -/

section Chosen

variable {S : Scheme.{u}} (B : BigFppfSite.{u}) (hS : B.Contains S)

/-- `Stacks.Adequate.pullbackSectionsSheafFunctor` retyped at the chosen big fppf site over `S`,
whose structure sheaf is the same sheaf of rings spelled through
`Stacks.Adequate.BigSite.toOver`. -/
public noncomputable def BigSite.pullbackSectionsSheafFunctor :
    (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory ⥤
      SheafOfModules.{u} (BigSite.ofBigFppfSite B S hS).structureSheaf :=
  Stacks.Adequate.pullbackSectionsSheafFunctor B S hS

/-- **The functor `u` of [Stacks, Tag 06VN] on the chosen big fppf site is the sections
construction of [Stacks, Tag 03DU] (3), naturally in the quasi-coherent module.** This is
`Stacks.Adequate.BigSite.associatedModuleFunctorObjIso` upgraded from an isomorphism at each
quasi-coherent module to an isomorphism of functors, which is what transporting a condition on a
*complex* of associated modules needs. -/
public noncomputable def BigSite.associatedModuleQcohIsoSections :
    (BigSite.ofBigFppfSite B S hS).associatedModuleQcoh ≅
      BigSite.pullbackSectionsSheafFunctor B hS :=
  Stacks.Adequate.associatedModuleQcohIsoSections B S hS

/-- The sections of the right-hand side over an object of the chosen big site are the global
sections of the pullback of `𝓖` to the scheme of that object, by definitional unfolding: that is
what `Stacks.Adequate.pullbackSectionsSheafFunctor` is. -/
public theorem BigSite.pullbackSectionsSheafFunctor_obj_val_obj
    (F : (SheafOfModules.isQuasicoherent S.ringCatSheaf).FullSubcategory)
    (Z : (BigSite.ofBigFppfSite B S hS).category) :
    ((((BigSite.pullbackSectionsSheafFunctor B hS).obj F).val.obj (op Z)) : Type u) =
      (Γ((Scheme.Modules.pullback
        ((BigSite.ofBigFppfSite B S hS).toOver.obj Z).hom).obj F.obj, ⊤) : Type u) := rfl

end Chosen

end Stacks.Adequate

end
