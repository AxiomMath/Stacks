module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleChartCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardPresentationExact
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.PushforwardOfAnInjective
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicAnySite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicGlobalSections
import all StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.PushforwardOfAnInjective

/-!
# Global sections of a direct image of modules along a morphism of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf site
`B`.  For every `𝒪_X`-module `𝓜` the global sections of the direct image are the global
sections of `𝓜`:

  `Γ(Y, f_*𝓜) = Γ(X, 𝓜)`,

naturally in `𝓜` and as abelian groups.  This is the identification behind reading the
derived functors of `Γ(Y, f_* −)` as the cohomology of `X`.

## Main definitions

* `AlgebraicGeometry.Space.sheafSectionsEquivHomFinal`: the sections of a sheaf of sets are the
  morphisms out of the final sheaf.
* `AlgebraicGeometry.Space.modulePushforwardSectionsEquiv`: `Γ(Y, f_*𝓜) ≃ Γ(X, 𝓜)`.
* `AlgebraicGeometry.Space.globalSectionsModulePushforwardIso`: the same as an isomorphism of
  functors to abelian groups, `Γ(Y, f_* −) ≅ Γ(X, −)`.

## Implementation notes

The argument is the topos-theoretic one.  Global sections of a sheaf of sets are morphisms out
of the final sheaf; the direct image of modules has, on the nose, the direct image of sheaves of
sets along the morphism of small étale topoi `AlgebraicGeometry.Space.smallToposMorphismTypeU`
as its underlying sheaf of sets; that direct image is right adjoint to an inverse image which
preserves finite limits, hence the final sheaf.  No representability of `f` is used.

The module structures of the two sides are over different rings, `Γ(Y, 𝒪_Y)` and `Γ(X, 𝒪_X)`,
so the identification is stated for the underlying abelian groups.  Additivity of the bijection
is `Stacks.Cohomology.naturalTransformationAddHom`: a natural transformation between the
underlying set-valued functors of two additive functors into abelian groups is additive.

## References

* [Stacks Project, Tag 0D2U](https://stacks.math.columbia.edu/tag/0D2U)
* [Stacks Project, Tag 0733](https://stacks.math.columbia.edu/tag/0733)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

universe u

namespace AlgebraicGeometry.Space

section FinalSheaf

variable {C : Type*} [Category.{u} C] (J : GrothendieckTopology C)

/-- The constant presheaf with value `PUnit` is a final presheaf of sets. -/
def isTerminalConstPUnit : IsTerminal ((Functor.const Cᵒᵖ).obj PUnit.{u + 1}) :=
  IsTerminal.ofUniqueHom (fun F => { app := fun X => Types.isTerminalPUnit.from (F.obj X) })
    (fun F m => NatTrans.ext (funext fun X => Types.isTerminalPUnit.hom_ext _ _))

/-- The final presheaf of sets, as a sheaf, is a final sheaf of sets. -/
def isTerminalFinalSheaf : IsTerminal (Stacks.Cohomology.finalSheaf.{u} J) :=
  IsTerminal.isTerminalOfObj (sheafToPresheaf J (Type u)) _ isTerminalConstPUnit

/-- The sections of a sheaf of sets are the morphisms out of the final sheaf. -/
def sheafSectionsEquivHomFinal (G : Sheaf J (Type u)) :
    G.obj.sections ≃ (Stacks.Cohomology.finalSheaf J ⟶ G) :=
  (G.obj.sectionsEquivHom PUnit).trans
    { toFun := fun τ => ⟨τ⟩
      invFun := fun g => g.hom
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/-- `AlgebraicGeometry.Space.sheafSectionsEquivHomFinal` is natural in the sheaf: the morphism out
of the final sheaf attached to the image of a section is the composite with the morphism of
sheaves. -/
lemma sheafSectionsEquivHomFinal_naturality {G H : Sheaf J (Type u)} (p : G ⟶ H)
    (s : G.obj.sections) :
    sheafSectionsEquivHomFinal J H ((Functor.sectionsFunctor Cᵒᵖ).map p.hom s) =
      sheafSectionsEquivHomFinal J G s ≫ p := rfl

variable {J} {D : Type*} [Category.{u} D] {K : GrothendieckTopology D}

/-- The inverse image of a morphism of topoi carries the final sheaf to the final sheaf, being
left exact. -/
def inverseImageFinalSheafIso (φ : MorphismOfTopoi (Sheaf J (Type u)) (Sheaf K (Type u))) :
    φ.inverseImage.obj (Stacks.Cohomology.finalSheaf K) ≅ Stacks.Cohomology.finalSheaf J :=
  have := φ.preservesFiniteLimits
  IsTerminal.uniqueUpToIso (IsTerminal.isTerminalObj _ _ (isTerminalFinalSheaf K))
    (isTerminalFinalSheaf J)

/-- **Global sections are unchanged by a direct image of sheaves of sets.**  For a morphism of
topoi `φ`, the sections of `φ_*G` are the sections of `G`: both are morphisms out of the final
sheaf, the inverse image is left adjoint to `φ_*`, and it preserves finite limits, hence the final
sheaf. -/
def pushforwardSectionsEquiv (φ : MorphismOfTopoi (Sheaf J (Type u)) (Sheaf K (Type u)))
    (G : Sheaf J (Type u)) : (φ.pushforward.obj G).obj.sections ≃ G.obj.sections :=
  (sheafSectionsEquivHomFinal K (φ.pushforward.obj G)).trans
    (((φ.adj.homEquiv _ _).symm.trans (inverseImageFinalSheafIso φ).homFromEquiv).trans
      (sheafSectionsEquivHomFinal J G).symm)

/-- The morphism out of the final sheaf attached to the section
`AlgebraicGeometry.Space.pushforwardSectionsEquiv φ G s` is the adjoint transpose of the one
attached to `s`, precomposed with the identification of the inverse image of the final sheaf. -/
lemma sheafSectionsEquivHomFinal_pushforwardSectionsEquiv
    (φ : MorphismOfTopoi (Sheaf J (Type u)) (Sheaf K (Type u))) (G : Sheaf J (Type u))
    (s : (φ.pushforward.obj G).obj.sections) :
    sheafSectionsEquivHomFinal J G (pushforwardSectionsEquiv φ G s) =
      (inverseImageFinalSheafIso φ).inv ≫
        (φ.adj.homEquiv _ _).symm (sheafSectionsEquivHomFinal K (φ.pushforward.obj G) s) := by
  rw [pushforwardSectionsEquiv, Equiv.trans_apply, Equiv.trans_apply, Equiv.apply_symm_apply]
  rfl

end FinalSheaf

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- **Global sections of a direct image of modules.**  For a morphism `f : X ⟶ Y` of algebraic
spaces and an `𝒪_X`-module `𝓜`, `Γ(Y, f_*𝓜) ≃ Γ(X, 𝓜)`: the underlying sheaf of sets of
`f_*𝓜` is the direct image of that of `𝓜` along the morphism of small étale topoi of `f`, and
`AlgebraicGeometry.Space.pushforwardSectionsEquiv` applies. -/
def modulePushforwardSectionsEquiv (f : X ⟶ Y) (M : Modules.{u, u} B S hS X.1 X.2) :
    ((modulePushforward B S hS f).obj M).sections ≃ M.sections :=
  pushforwardSectionsEquiv (smallToposMorphismTypeU B S hS f) (moduleSetSheaf B S hS X M)

/-- `AlgebraicGeometry.Space.modulePushforwardSectionsEquiv` is natural in the module. -/
lemma modulePushforwardSectionsEquiv_naturality (f : X ⟶ Y)
    {M N : Modules.{u, u} B S hS X.1 X.2} (q : M ⟶ N)
    (s : ((modulePushforward B S hS f).obj M).sections) :
    modulePushforwardSectionsEquiv B S hS f N
        (SheafOfModules.sectionsMap ((modulePushforward B S hS f).map q) s) =
      SheafOfModules.sectionsMap q (modulePushforwardSectionsEquiv B S hS f M s) := by
  let φ := smallToposMorphismTypeU B S hS f
  let g : moduleSetSheaf B S hS X M ⟶ moduleSetSheaf B S hS X N :=
    (sheafCompose (SmallEtale.topology B S hS X.1) (forget AddCommGrpCat.{u})).map
      ((SheafOfModules.toSheaf _).map q)
  apply (sheafSectionsEquivHomFinal (SmallEtale.topology B S hS X.1)
    (moduleSetSheaf B S hS X N)).injective
  calc sheafSectionsEquivHomFinal _ (moduleSetSheaf B S hS X N)
        (modulePushforwardSectionsEquiv B S hS f N
          (SheafOfModules.sectionsMap ((modulePushforward B S hS f).map q) s))
      = (inverseImageFinalSheafIso φ).inv ≫ (φ.adj.homEquiv _ _).symm
          (sheafSectionsEquivHomFinal _ (φ.pushforward.obj (moduleSetSheaf B S hS X N))
            (SheafOfModules.sectionsMap ((modulePushforward B S hS f).map q) s)) :=
        sheafSectionsEquivHomFinal_pushforwardSectionsEquiv φ _ _
    _ = (inverseImageFinalSheafIso φ).inv ≫ (φ.adj.homEquiv _ _).symm
          (sheafSectionsEquivHomFinal _ (φ.pushforward.obj (moduleSetSheaf B S hS X M)) s ≫
            φ.pushforward.map g) := rfl
    _ = ((inverseImageFinalSheafIso φ).inv ≫ (φ.adj.homEquiv _ _).symm
          (sheafSectionsEquivHomFinal _ (φ.pushforward.obj (moduleSetSheaf B S hS X M)) s)) ≫ g :=
        by rw [Adjunction.homEquiv_naturality_right_symm, Category.assoc]
    _ = sheafSectionsEquivHomFinal _ (moduleSetSheaf B S hS X M)
          (modulePushforwardSectionsEquiv B S hS f M s) ≫ g :=
        congrArg (· ≫ g) (sheafSectionsEquivHomFinal_pushforwardSectionsEquiv φ _ s).symm
    _ = _ := rfl

/-- The global sections of `𝒪_Y`-modules after the direct image, read in abelian groups. -/
abbrev pushforwardGlobalSectionsAb (f : X ⟶ Y) :
    Modules.{u, u} B S hS X.1 X.2 ⥤ AddCommGrpCat.{u + 1} :=
  modulePushforward B S hS f ⋙
    Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O) ⋙
    forget₂ _ AddCommGrpCat.{u + 1}

/-- The global sections of `𝒪_X`-modules, read in abelian groups. -/
abbrev globalSectionsAb (X : AlgebraicSpaces B S hS) :
    Modules.{u, u} B S hS X.1 X.2 ⥤ AddCommGrpCat.{u + 1} :=
  Stacks.Cohomology.SiteModules.globalSectionsFunctor.{u + 1, u, u, u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) ⋙
    forget₂ _ AddCommGrpCat.{u + 1}

/-- The global sections of the direct image, read in abelian groups, form an additive functor. -/
instance (f : X ⟶ Y) : (pushforwardGlobalSectionsAb B S hS f).Additive := by
  have := modulePushforward_additive B S hS f
  infer_instance

/-- `AlgebraicGeometry.Space.modulePushforwardSectionsEquiv` as a natural transformation of the
underlying set-valued functors. -/
def modulePushforwardSectionsNatTrans (f : X ⟶ Y) :
    pushforwardGlobalSectionsAb B S hS f ⋙ forget AddCommGrpCat.{u + 1} ⟶
      globalSectionsAb B S hS X ⋙ forget AddCommGrpCat.{u + 1} where
  app M := ↾(modulePushforwardSectionsEquiv B S hS f M)
  naturality M N q := by
    ext s
    exact modulePushforwardSectionsEquiv_naturality B S hS f q s

/-- **`Γ(Y, f_* −) ≅ Γ(X, −)` as functors to abelian groups**, for any morphism `f : X ⟶ Y` of
algebraic spaces. -/
def globalSectionsModulePushforwardIso (f : X ⟶ Y) :
    pushforwardGlobalSectionsAb B S hS f ≅ globalSectionsAb B S hS X :=
  NatIso.ofComponents
    (fun M => (AddEquiv.mk' (modulePushforwardSectionsEquiv B S hS f M)
      (Stacks.Cohomology.naturalTransformationAddHom _ _
        (modulePushforwardSectionsNatTrans B S hS f) M).map_add).toAddCommGrpIso)
    (fun {M N} q => by
      ext s
      exact modulePushforwardSectionsEquiv_naturality B S hS f q s)

end AlgebraicGeometry.Space

end
