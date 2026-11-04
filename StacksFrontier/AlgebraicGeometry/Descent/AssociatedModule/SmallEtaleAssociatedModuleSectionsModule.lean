module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleAssociatedModuleSectionsUnit
public import StacksFrontier.AlgebraicGeometry.Topologies.AssociatedModuleFunctor

/-!
# The associated module on the small étale site is natural in the module

`AlgebraicGeometry.SmallEtale.associatedModulePresheafIso` identifies the abelian presheaf
underlying `𝓕^a` with the presheaf of **Stacks 03DS** of `𝓕`, on the small étale site of `S`.
`AlgebraicGeometry.SmallEtale.associatedModulePresheafIso_hom_naturality` says that
identification carries the restriction maps of `𝓕^a` to the restriction maps of the presheaf of
Stacks 03DS — naturality in the *arrow of the site*. This file proves the other naturality: for
a morphism `φ : 𝓕 ⟶ 𝓖` of quasi-coherent `𝒪_S`-modules, the identification carries `φ^a` to the
map on pullback sections induced by `φ`.

Both naturalities are needed by the proof of **Stacks 076T**, and for the same reason: the
cocycle condition for the sections identification
`AlgebraicGeometry.Stack.liftedSectionsIso` compares two arrows of `𝒳` lying over two different
schemes `W` and `W'`, so its last factor has to move between `(g^*𝓕)^a` on `W_ét` and
`(g'^*𝓕)^a` on `W'_ét`. The vertical map at the associated-module stage factors through
`AlgebraicGeometry.SmallEtale.associatedModule` applied to a *morphism of modules* — the
composition law `AlgebraicGeometry.Scheme.Modules.pullbackFactoredComp` for the pullbacks of
modules on the schemes below — while the corresponding vertical at the sections stage is
`Stacks.Sites.pullbackCompSectionsIsoOfEq`, which by construction is the map on global sections
induced by that same morphism of modules. Only naturality in the module relates the two.

## The statement is pointwise, and needs no packaging

`AlgebraicGeometry.SmallEtale.sectionsPresheafOfModules` takes quasi-coherence as an instance
argument, so a *functor* form of the identification would first have to be packaged on the full
subcategory of quasi-coherent modules. No functor is needed: the commuting square for a single
morphism `φ : 𝓕 ⟶ 𝓖` is statable with both quasi-coherence instances in scope, and that is the
form below. What the proof does use is
`AlgebraicGeometry.pullbackSectionsFunctor` — Stacks 03DS as a functor in the module — for the
map on the sections side.

## The proof

Three of the four factors of the identification are natural in the module for free, and the
fourth is a transposition:

* `AlgebraicGeometry.SmallEtale.associatedModuleSheafificationIso` is an isomorphism of
  *functors*, so its naturality is `CategoryTheory.NatTrans.naturality`;
* the sheafification unit is a natural transformation, so its naturality is the same;
* `CategoryTheory.PresheafOfModules.sheafification` is a functor, so it carries the remaining
  square across;
* the comparison `AlgebraicGeometry.SmallEtale.sectionsComparison` of **Stacks 070S (2)** is
  the transpose of `AlgebraicGeometry.SmallEtale.sectionsUnit` along
  `CategoryTheory.PresheafOfModules.pullbackPushforwardAdjunction`, so its naturality is the
  naturality of that transpose, which is naturality of `sectionsUnit` itself — and that, on
  components, is `AlgebraicGeometry.Scheme.Modules.pullbackSection_naturality`: pulling a
  section back commutes with a morphism of modules.

## Main definitions

* `AlgebraicGeometry.SmallEtale.sectionsPresheafOfModulesMap`: the map of pullback-sections
  presheaves of modules induced by a morphism of quasi-coherent modules.

## Main results

* `AlgebraicGeometry.SmallEtale.sectionsUnit_naturality_module` and
  `AlgebraicGeometry.SmallEtale.sectionsComparison_naturality_module`: the two inputs.
* `AlgebraicGeometry.SmallEtale.associatedModuleIsoSections_hom_naturality_module` and
  `AlgebraicGeometry.SmallEtale.associatedModuleIsoSectionsPresheaf_hom_naturality_module`:
  Stacks 070S on the small étale site is natural in the module, before and after stripping the
  sheafification.
* `AlgebraicGeometry.SmallEtale.associatedModulePresheafIso_hom_naturality_module`: **the
  identification of `𝓕^a` with the presheaf of Stacks 03DS is natural in the module.**

## References

* [Stacks Project, Tag 070S](https://stacks.math.columbia.edu/tag/070S)
* [Stacks Project, Tag 03DS](https://stacks.math.columbia.edu/tag/03DS)
* [Stacks Project, Tag 03DU](https://stacks.math.columbia.edu/tag/03DU)
* [Stacks Project, Tag 076T](https://stacks.math.columbia.edu/tag/076T)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.SmallEtale

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The pullback-sections presheaf of modules is functorial in the module.**  A morphism
`φ : 𝓕 ⟶ 𝓖` of quasi-coherent `𝒪_S`-modules induces, over each object `T / S` of the small étale
site, the map `Γ(T, T^⁺𝓕) ⟶ Γ(T, T^⁺𝓖)` on global sections of the pullbacks.

The underlying map of abelian presheaves is `Stacks.Sites.associatedPresheafMap`, i.e.
`AlgebraicGeometry.pullbackSectionsFunctor` — Stacks 03DS as a functor in the module —
restricted along `AlgebraicGeometry.SmallEtale.toOver`; its linearity over the global functions
on each object of the site is `AlgebraicGeometry.Scheme.Modules.Hom.app_smul`. -/
public noncomputable def sectionsPresheafOfModulesMap {F G : S.Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G) :
    sectionsPresheafOfModules B S hS F ⟶ sectionsPresheafOfModules B S hS G :=
  PresheafOfModules.homMk (Stacks.Sites.associatedPresheafMap S (toOver B S hS) φ)
    fun _ r m => Scheme.Modules.Hom.app_smul _ r m

/-- **Pulling sections back is natural in the module.**  The morphism
`AlgebraicGeometry.SmallEtale.sectionsUnit`, which sends a section of `𝓕` over an open `U` of
`S` to its pullback to the open subscheme `U`, commutes with a morphism `φ : 𝓕 ⟶ 𝓖` of
quasi-coherent modules.

On components this is `AlgebraicGeometry.Scheme.Modules.pullbackSection_naturality`: the
pullback of `φ.app U a` is the image under `φ` pulled back of the pullback of `a`. -/
public theorem sectionsUnit_naturality_module {F G : S.Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G) :
    (SheafOfModules.forget S.ringCatSheaf).map φ ≫ sectionsUnit B S hS G =
      sectionsUnit B S hS F ≫ (PresheafOfModules.pushforward.{u}
        (structureMap B S hS).hom).map (sectionsPresheafOfModulesMap B S hS φ) := by
  refine PresheafOfModules.Hom.ext ?_
  ext U a
  exact (Scheme.Modules.pullbackSection_naturality (Scheme.Opens.ι U.unop) φ U.unop ⊤
    (Scheme.Opens.top_le_ι_preimage le_rfl) a).symm

/-- **The comparison of Stacks 070S (2) is natural in the module.**  For a morphism
`φ : 𝓕 ⟶ 𝓖` of quasi-coherent `𝒪_S`-modules, the Stacks 06WC-style pullback of `φ` followed by
the comparison at `𝓖` is the comparison at `𝓕` followed by the induced map of pullback-sections
presheaves.

`AlgebraicGeometry.SmallEtale.sectionsComparison` is the transpose of
`AlgebraicGeometry.SmallEtale.sectionsUnit` along
`CategoryTheory.PresheafOfModules.pullbackPushforwardAdjunction`, so this square is the square
for `sectionsUnit` transposed: both `CategoryTheory.Adjunction.homEquiv_naturality_left_symm`
and `CategoryTheory.Adjunction.homEquiv_naturality_right_symm` apply, and what is left is
`AlgebraicGeometry.SmallEtale.sectionsUnit_naturality_module`. -/
public theorem sectionsComparison_naturality_module {F G : S.Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G) :
    (PresheafOfModules.pullback.{u} (structureMap B S hS).hom).map
          ((SheafOfModules.forget S.ringCatSheaf).map φ) ≫
        sectionsComparison B S hS G =
      sectionsComparison B S hS F ≫ sectionsPresheafOfModulesMap B S hS φ := by
  unfold sectionsComparison
  rw [← Adjunction.homEquiv_naturality_left_symm, ← Adjunction.homEquiv_naturality_right_symm,
    sectionsUnit_naturality_module]

/-- **Stacks 070S on the small étale site is natural in the module.**  For a morphism
`φ : 𝓕 ⟶ 𝓖` of quasi-coherent `𝒪_S`-modules, the identification of `𝓕^a` with the
sheafification of the pullback-sections presheaf carries `φ^a` to the sheafification of the map
of pullback-sections presheaves induced by `φ`.

Two of the identification's factors supply this at once:
`AlgebraicGeometry.SmallEtale.associatedModuleSheafificationIso` is an isomorphism of *functors*
on `S.Modules`, so its naturality is available, and the remaining factor is
`CategoryTheory.PresheafOfModules.sheafification` applied to
`AlgebraicGeometry.SmallEtale.sectionsComparison`, whose naturality in the module is
`AlgebraicGeometry.SmallEtale.sectionsComparison_naturality_module`. -/
public theorem associatedModuleIsoSections_hom_naturality_module {F G : S.Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G) :
    (associatedModule B S hS).map φ ≫ (associatedModuleIsoSections B S hS G).hom =
      (associatedModuleIsoSections B S hS F).hom ≫
        (PresheafOfModules.sheafification.{u} (𝟙 (structureSheaf B S hS).obj)).map
          (sectionsPresheafOfModulesMap B S hS φ) := by
  unfold associatedModuleIsoSections
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
            (sectionsPresheafOfModulesMap B S hS φ) := by
    rw [← Functor.map_comp, ← Functor.map_comp, sectionsComparison_naturality_module]
  rw [← Category.assoc, (associatedModuleSheafificationIso B S hS).hom.naturality φ]
  simp only [Category.assoc]
  exact congrArg (fun t => (associatedModuleSheafificationIso B S hS).hom.app F ≫ t) key


/-- The category algebra of conjugating a naturality square by an invertible natural
transformation, with every object and arrow abstract: `h1` is the square before conjugation,
`h2` the naturality of the transformation being inverted, and the two inverse laws say that
transformation is invertible at both ends.

Stating it abstractly keeps the application a single `exact`, which unifies up to definitional
equality: the right adjoint of `CategoryTheory.PresheafOfModules.sheafification` is a composite
of two functors, and the naturality of the sheafification unit records its middle object in the
composite spelling while the isomorphism inverted here records it in the applied one. -/
private theorem unit_conjugate_algebra {C : Type*} [Category C] {O₁ O₂ O₃ O₄ O₅ O₆ : C}
    (m : O₁ ⟶ O₂) (aF : O₁ ⟶ O₃) (aG : O₂ ⟶ O₄) (sh : O₃ ⟶ O₄)
    (uFhom : O₅ ⟶ O₃) (uFinv : O₃ ⟶ O₅) (uGhom : O₆ ⟶ O₄) (uGinv : O₄ ⟶ O₆)
    (sg : O₅ ⟶ O₆)
    (h1 : m ≫ aG = aF ≫ sh) (h2 : uFhom ≫ sh = sg ≫ uGhom)
    (hF : uFinv ≫ uFhom = 𝟙 O₃) (hG : uGhom ≫ uGinv = 𝟙 O₆) :
    m ≫ aG ≫ uGinv = (aF ≫ uFinv) ≫ sg := by
  rw [← Category.assoc, h1, Category.assoc, Category.assoc]
  refine congrArg (fun t => aF ≫ t) ?_
  calc sh ≫ uGinv
      = uFinv ≫ uFhom ≫ sh ≫ uGinv := by
        rw [← Category.assoc uFinv uFhom, hF, Category.id_comp]
    _ = uFinv ≫ sg ≫ uGhom ≫ uGinv := by
        rw [← Category.assoc uFhom sh, h2, Category.assoc]
    _ = uFinv ≫ sg := by rw [hG, Category.comp_id]

/-- **Stacks 070S on the small étale site, with the sheafification stripped, is natural in the
module.**  `AlgebraicGeometry.SmallEtale.associatedModuleIsoSectionsPresheaf` inverts the
sheafification unit at the pullback-sections presheaf, which is a sheaf there; since the unit is
a natural transformation, inverting it preserves the naturality of
`AlgebraicGeometry.SmallEtale.associatedModuleIsoSections_hom_naturality_module`. -/
public theorem associatedModuleIsoSectionsPresheaf_hom_naturality_module {F G : S.Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G) :
    (SheafOfModules.forget (structureSheaf B S hS) ⋙
          PresheafOfModules.restrictScalars (𝟙 (structureSheaf B S hS).obj)).map
          ((associatedModule B S hS).map φ) ≫
        (associatedModuleIsoSectionsPresheaf B S hS G).hom =
      (associatedModuleIsoSectionsPresheaf B S hS F).hom ≫
        sectionsPresheafOfModulesMap B S hS φ := by
  have h1 := congrArg (SheafOfModules.forget (structureSheaf B S hS) ⋙
    PresheafOfModules.restrictScalars (𝟙 (structureSheaf B S hS).obj)).map
    (associatedModuleIsoSections_hom_naturality_module B S hS φ)
  simp only [Functor.map_comp] at h1
  let eF := @asIso _ _ _ _ _ (isIso_sheafificationAdjunction_unit_app B S hS _
    (isSheaf_sectionsPresheafOfModules B S hS F))
  let eG := @asIso _ _ _ _ _ (isIso_sheafificationAdjunction_unit_app B S hS _
    (isSheaf_sectionsPresheafOfModules B S hS G))
  exact unit_conjugate_algebra _ _ _ _ eF.hom eF.inv eG.hom eG.inv _ h1
    ((PresheafOfModules.sheafificationAdjunction
      (𝟙 (structureSheaf B S hS).obj)).unit.naturality
        (sectionsPresheafOfModulesMap B S hS φ)).symm eF.inv_hom_id eG.hom_inv_id


/-- **The identification of `𝓕^a` with the presheaf of Stacks 03DS is natural in the module.**
For a morphism `φ : 𝓕 ⟶ 𝓖` of quasi-coherent `𝒪_S`-modules and an object `W` of the small étale
site of `S`, reading a section of `𝓕^a` over `W` as a pullback section and then applying `φ` is
applying `φ^a` first and reading afterwards.

This is the companion of `AlgebraicGeometry.SmallEtale.associatedModulePresheafIso_hom_naturality`,
which is the same statement for an arrow of the site rather than for a morphism of modules.

No packaging on the full subcategory of quasi-coherent modules is required: the square is
stated for one morphism, with both quasi-coherence instances in scope. -/
public theorem associatedModulePresheafIso_hom_naturality_module {F G : S.Modules}
    [F.IsQuasicoherent] [G.IsQuasicoherent] (φ : F ⟶ G) (W : (SmallEtale B S hS)ᵒᵖ) :
    ((PresheafOfModules.toPresheaf (structureSheaf B S hS).obj).map
            ((SheafOfModules.forget (structureSheaf B S hS)).map
              ((associatedModule B S hS).map φ))).app W ≫
        (associatedModulePresheafIso B S hS G).hom.app W =
      (associatedModulePresheafIso B S hS F).hom.app W ≫
        ((Scheme.Modules.pullback ((toOver B S hS).obj W.unop).hom).map φ).app ⊤ := by
  have key := congrArg
    (fun t => ((PresheafOfModules.toPresheaf (structureSheaf B S hS).obj).map t).app W)
    (associatedModuleIsoSectionsPresheaf_hom_naturality_module B S hS φ)
  simp only [Functor.map_comp, NatTrans.comp_app] at key
  exact key

end AlgebraicGeometry.SmallEtale

end
