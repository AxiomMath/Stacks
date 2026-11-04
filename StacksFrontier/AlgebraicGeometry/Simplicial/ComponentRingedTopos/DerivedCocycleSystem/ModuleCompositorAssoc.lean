module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedPullbackComposition
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedModuleSystem
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianPair
public import StacksFrontier.CategoryTheory.Sites.Simplicial.PushforwardCoherence
public import Mathlib.CategoryTheory.Adjunction.CompositionIso

/-!
# The cocycle law for the compositors of direct images and pullbacks of modules

Let `S` be a simplicial-site situation (Stacks 09WE) and `O` a sheaf of commutative rings on its
total site. The cartesian simplicial system of Stacks 0GMF
(the sibling file `DerivedCocycleSystem/CocyclePairSystem.lean`)
needs the compositor of derived pullbacks to be coherent — the cocycle, or pentagon, law

`Lf_φ^*(c_{χ,ψ}) ∘ c_{χ ≫ ψ, φ} = c_{ψ,φ} ∘ c_{χ, ψ ≫ φ}`.

That law is proved by climbing a ladder of five rungs. This file climbs the first four; the last,
the passage to the derived categories, is
the sibling file `DerivedCocycleSystem/DerivedCompositorAssoc.lean`.

The bottom rung, the law for the direct images of sheaves of *sets*, is Stacks 09WE and is
already available (`CategoryTheory.SimplicialSiteSituation.pushforwardCompSymm_assoc`). It is
carried to the direct images of sheaves of *modules* by faithfulness: the comparison of direct
images of modules *is* the geometric compositor on underlying sheaves of sets. It is carried from
there to the *pullbacks* of modules by `CategoryTheory.Adjunction.leftAdjointCompIso_assoc`, the
comparison of pullbacks being the adjoint mate of the comparison of direct images. It passes
degreewise to the unbounded homotopy categories.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.componentModuleSheaf`,
  `.transitionPushforwardModules`, `.transitionPullbackAdj`,
  `.transitionPullbackHomotopy` and `.transitionPullbackHomotopyComp`: the intermediate levels
  of the ladder.

## Main results

* `CategoryTheory.SimplicialSiteSituation.transitionPushforwardModulesCompIso_assoc`,
  `.transitionPullbackModulesCompIso_assoc` and `.transitionPullbackHomotopyComp_assoc`: the law
  on the lower rungs.
* `CategoryTheory.SimplicialSiteSituation.transitionPullbackModulesCompIso_eq_leftAdjointCompIso`:
  the comparison of pullbacks of sheaves of modules is the adjoint mate of the comparison of
  direct images, which is what lets the law be transported to the left adjoints.
* `CategoryTheory.mapHomotopyCategoryCompIso_hom_app_assoc` and
  `.mapHomotopyCategoryCompIso_hom_assoc`: a cocycle law for compositors of additive functors
  passes to the unbounded homotopy categories.
* `CategoryTheory.Adjunction.leftAdjointUniq_ofNatIsoRight_hom`: the comparison of two left
  adjoints of one functor, one of them presented through a transport of its right adjoint, as a
  conjugate.

## Implementation notes

*Why the pullback law is deduced from the direct-image law.* The comparison of pullbacks of
sheaves of modules is defined as the adjoint mate of the comparison of direct images
(`Stacks.Sheaves.RingedToposModules.pullbackModulesCompIso`), so no direct proof of its cocycle
law is available; the mate of a cocycle law is a cocycle law, which is
`CategoryTheory.Adjunction.leftAdjointCompIso_assoc`, and the only thing to check is that the
definition really is the mate. That is
`transitionPullbackModulesCompIso_eq_leftAdjointCompIso`, proved by comparing conjugates.

*Generic lemmas whose objects are free variables.* `mapHomotopyCategoryCompIso_hom_app_assoc` is
the generic form of the homotopy-category rung and `mapHomotopyCategoryCompIso_hom_assoc` its
natural-transformation form; the concrete law is one application of the latter. Stating that rung
at the level of natural transformations rather than at an object is what makes it elaborate at
all: it removes the type of the complex and the `.app`-level re-synthesis of the additivity
instances. The further devices used here are recorded in the implementation notes of
the sibling file `DerivedCocycleSystem/DerivedCompositorAssoc.lean`.

## References

* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPushforward
open Stacks.Sheaves.RingedToposModules (pushforwardModules
  pullbackAdjPushforwardModules hom_ext_moduleSheafFunctor
  moduleSheafFunctor_map_pushforwardModules_map)
open scoped Simplicial

universe u

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory

section HomotopyCompositor

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {C₀ : Type u₁} [Category.{v₁} C₀] [Preadditive C₀]
  {C₁ : Type u₂} [Category.{v₂} C₁] [Preadditive C₁]
  {C₂ : Type u₃} [Category.{v₃} C₂] [Preadditive C₂]
  {C₃ : Type u₄} [Category.{v₄} C₃] [Preadditive C₃]
  {F₀₁ : C₀ ⥤ C₁} {F₁₂ : C₁ ⥤ C₂} {F₂₃ : C₂ ⥤ C₃}
  {F₀₂ : C₀ ⥤ C₂} {F₁₃ : C₁ ⥤ C₃} {F₀₃ : C₀ ⥤ C₃}
  [F₀₁.Additive] [F₁₂.Additive] [F₂₃.Additive]
  [F₀₂.Additive] [F₁₃.Additive] [F₀₃.Additive]

/-- **A cocycle law for compositors of additive functors passes to the unbounded homotopy
categories.** Both sides are the image under the quotient functor of the corresponding composite
of comparisons of complexes, and those agree because they agree degreewise. -/
theorem mapHomotopyCategoryCompIso_hom_app_assoc (e₀₁₂ : F₀₁ ⋙ F₁₂ ≅ F₀₂)
    (e₁₂₃ : F₁₂ ⋙ F₂₃ ≅ F₁₃) (e₀₁₃ : F₀₁ ⋙ F₁₃ ≅ F₀₃) (e₀₂₃ : F₀₂ ⋙ F₂₃ ≅ F₀₃)
    (h : ∀ X, F₂₃.map (e₀₁₂.hom.app X) ≫ e₀₂₃.hom.app X =
      e₁₂₃.hom.app (F₀₁.obj X) ≫ e₀₁₃.hom.app X)
    (K : HomotopyCategory C₀ (ComplexShape.up ℤ)) :
    (F₂₃.mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((Functor.mapHomotopyCategoryCompIso e₀₁₂ (ComplexShape.up ℤ)).hom.app K) ≫
        (Functor.mapHomotopyCategoryCompIso e₀₂₃ (ComplexShape.up ℤ)).hom.app K =
      (Functor.mapHomotopyCategoryCompIso e₁₂₃ (ComplexShape.up ℤ)).hom.app
          ((F₀₁.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
        (Functor.mapHomotopyCategoryCompIso e₀₁₃ (ComplexShape.up ℤ)).hom.app K := by
  obtain ⟨K⟩ := K
  have key : (F₂₃.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((Functor.mapHomologicalComplexCompIso e₀₁₂ (ComplexShape.up ℤ)).hom.app K) ≫
        (Functor.mapHomologicalComplexCompIso e₀₂₃ (ComplexShape.up ℤ)).hom.app K =
      (Functor.mapHomologicalComplexCompIso e₁₂₃ (ComplexShape.up ℤ)).hom.app
          ((F₀₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        (Functor.mapHomologicalComplexCompIso e₀₁₃ (ComplexShape.up ℤ)).hom.app K := by
    ext i
    simpa using h (K.X i)
  simp only [Functor.mapHomotopyCategoryCompIso]
  exact congrArg (HomotopyCategory.quotient C₃ (ComplexShape.up ℤ)).map key

/-- **A cocycle law for compositors of additive functors passes to the unbounded homotopy
categories**, as an equality of natural transformations. This is the form the simplicial
compositors are used in; it is `mapHomotopyCategoryCompIso_hom_app_assoc` read at every
object. -/
theorem mapHomotopyCategoryCompIso_hom_assoc (e₀₁₂ : F₀₁ ⋙ F₁₂ ≅ F₀₂)
    (e₁₂₃ : F₁₂ ⋙ F₂₃ ≅ F₁₃) (e₀₁₃ : F₀₁ ⋙ F₁₃ ≅ F₀₃) (e₀₂₃ : F₀₂ ⋙ F₂₃ ≅ F₀₃)
    (h : ∀ X, F₂₃.map (e₀₁₂.hom.app X) ≫ e₀₂₃.hom.app X =
      e₁₂₃.hom.app (F₀₁.obj X) ≫ e₀₁₃.hom.app X) :
    Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso e₀₁₂ (ComplexShape.up ℤ)).hom
            (F₂₃.mapHomotopyCategory (ComplexShape.up ℤ)) ≫
          (Functor.mapHomotopyCategoryCompIso e₀₂₃ (ComplexShape.up ℤ)).hom =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (F₀₁.mapHomotopyCategory (ComplexShape.up ℤ))
            (Functor.mapHomotopyCategoryCompIso e₁₂₃ (ComplexShape.up ℤ)).hom ≫
          (Functor.mapHomotopyCategoryCompIso e₀₁₃ (ComplexShape.up ℤ)).hom := by
  ext K
  simpa using mapHomotopyCategoryCompIso_hom_app_assoc e₀₁₂ e₁₂₃ e₀₁₃ e₀₂₃ h K

/-- Composing a compositor of additive functors with a further isomorphism, read on the
unbounded homotopy categories. -/
theorem mapHomotopyCategoryCompIso_trans_hom_app {F₀₂' : C₀ ⥤ C₂} [F₀₂'.Additive]
    (e : F₀₁ ⋙ F₁₂ ≅ F₀₂) (t : F₀₂ ≅ F₀₂') (K : HomotopyCategory C₀ (ComplexShape.up ℤ)) :
    (Functor.mapHomotopyCategoryCompIso (e ≪≫ t) (ComplexShape.up ℤ)).hom.app K =
      (Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom.app K ≫
        (NatTrans.mapHomotopyCategory t.hom (ComplexShape.up ℤ)).app K := by
  obtain ⟨K⟩ := K
  rfl

end HomotopyCompositor

namespace Adjunction

/-- The comparison of two left adjoints of one functor, one of them presented through a
transport of its right adjoint, as a conjugate: this is what identifies the comparison of
pullbacks of sheaves of modules with the adjoint mate of the comparison of direct images. -/
theorem leftAdjointUniq_ofNatIsoRight_hom {C D : Type*} [Category C] [Category D]
    {L₁ L₂ : C ⥤ D} {R₁ R₂ : D ⥤ C} (a : L₁ ⊣ R₁) (b : L₂ ⊣ R₂) (e : R₁ ≅ R₂) :
    (Adjunction.leftAdjointUniq (a.ofNatIsoRight e) b).hom =
      (conjugateEquiv b a).symm e.inv := by
  ext X
  simp [Adjunction.leftAdjointUniq, conjugateEquiv_symm_apply_app, Adjunction.ofNatIsoRight]

end Adjunction

end CategoryTheory

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

/-! ### The underlying sheaves of sets of the modules on a component -/

/-- Degreewise direct image of sheaves of modules along the transition morphism of a simplex
map, named for the coherence statements of this file. -/
abbrev transitionPushforwardModules {m n : SimplexCategory} (φ : m ⟶ n) :=
  pushforwardModules.{u, u, u, u, u, u} (S.transitionRingedToposHom O φ).toModulesHom

/-- The underlying sheaf of sets of a sheaf of modules on the component in simplicial degree
`n`. It is `CategoryTheory.Sheaf.moduleSheafFunctor` with the component topology written out:
the ascription is what lets the coherence statements below compose it with the direct images of
sheaves of sets without unfolding the component ringed topos. -/
def componentModuleSheaf (n : SimplexCategory) :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O n).O) ⥤
      Sheaf (S.componentTopology n) (Type u) :=
  Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O n).O)

/-- A morphism of sheaves of modules on a component is determined by the underlying morphism of
sheaves of sets. -/
theorem componentModuleSheaf_hom_ext {n : SimplexCategory}
    {M N : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O n).O)} {α β : M ⟶ N}
    (h : (S.componentModuleSheaf O n).map α = (S.componentModuleSheaf O n).map β) : α = β := by
  apply hom_ext_moduleSheafFunctor
  exact h

/-- The underlying sheaf-of-sets map of the direct image of a morphism of sheaves of modules
along a transition morphism is the direct image of the underlying map. -/
theorem componentModuleSheaf_transitionPushforwardModules_map {m n : SimplexCategory}
    (φ : m ⟶ n)
    {M N : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O n).O)} (α : M ⟶ N) :
    (S.componentModuleSheaf O m).map ((S.transitionPushforwardModules O φ).map α) =
      (S.transitionMorphism φ).pushforward.map ((S.componentModuleSheaf O n).map α) :=
  moduleSheafFunctor_map_pushforwardModules_map
    (S.transitionRingedToposHom O φ).toModulesHom α

/-- The underlying sheaf-of-sets map of the comparison of direct images of sheaves of modules
is the geometric compositor of Stacks 09WE. -/
theorem componentModuleSheaf_transitionPushforwardModulesCompIso_hom {l m n : SimplexCategory}
    (ψ : l ⟶ m) (φ : m ⟶ n)
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O n).O)) :
    (S.componentModuleSheaf O l).map
        ((S.transitionPushforwardModulesCompIso O ψ φ).hom.app M) =
      (S.pushforwardCompSymm ψ φ).hom.app ((S.componentModuleSheaf O n).obj M) :=
  S.moduleSheaf_transitionPushforwardModulesCompIso_hom O ψ φ M

/-! ### Associativity of the compositor of direct images of sheaves of sets -/

/-- The cocycle law for the direct-image compositors of Stacks 09WE, read at a sheaf. The two
spellings of the triple composite agree because composition in the simplex category is
associative by `rfl`, so no transport appears. -/
theorem pushforwardCompSymm_assoc_app {k l m n : SimplexCategory} (χ : k ⟶ l) (ψ : l ⟶ m)
    (φ : m ⟶ n) (X : Sheaf (S.componentTopology n) (Type u)) :
    (S.pushforwardCompSymm χ ψ).hom.app ((S.transitionMorphism φ).pushforward.obj X) ≫
        (S.pushforwardCompSymm (χ ≫ ψ) φ).hom.app X =
      (S.transitionMorphism χ).pushforward.map ((S.pushforwardCompSymm ψ φ).hom.app X) ≫
        (S.pushforwardCompSymm χ (ψ ≫ φ)).hom.app X := by
  have h := NatTrans.congr_app (congrArg Iso.hom (S.pushforwardCompSymm_assoc χ ψ φ)) X
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Iso.symm_hom, Functor.associator_inv_app, Category.id_comp] at h
  have hB : (S.pushforwardCompSymm (χ ≫ ψ) φ).hom.app X ≫
        (S.pushforwardCongr (Category.assoc χ ψ φ)).hom.app X =
      (S.pushforwardCompSymm (χ ≫ ψ) φ).hom.app X := Category.comp_id _
  exact (congrArg (fun t ↦ (S.pushforwardCompSymm χ ψ).hom.app
    ((S.transitionMorphism φ).pushforward.obj X) ≫ t) hB).symm.trans h

/-- The cocycle law for the geometric compositors, at the underlying sheaf of sets of a sheaf of
modules. -/
theorem pushforwardCompSymm_assoc_componentModuleSheaf {k l m n : SimplexCategory} (χ : k ⟶ l)
    (ψ : l ⟶ m) (φ : m ⟶ n)
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O n).O)) :
    (S.pushforwardCompSymm χ ψ).hom.app
          ((S.componentModuleSheaf O m).obj ((S.transitionPushforwardModules O φ).obj M)) ≫
        (S.pushforwardCompSymm (χ ≫ ψ) φ).hom.app ((S.componentModuleSheaf O n).obj M) =
      (S.transitionMorphism χ).pushforward.map
          ((S.pushforwardCompSymm ψ φ).hom.app ((S.componentModuleSheaf O n).obj M)) ≫
        (S.pushforwardCompSymm χ (ψ ≫ φ)).hom.app ((S.componentModuleSheaf O n).obj M) :=
  S.pushforwardCompSymm_assoc_app χ ψ φ ((S.componentModuleSheaf O n).obj M)

/-- The direct image along `f_χ` of the underlying sheaf-of-sets map of the comparison of direct
images of modules is the direct image along `f_χ` of the geometric compositor. -/
theorem transitionMorphism_map_componentModuleSheaf_compIso {k l m n : SimplexCategory}
    (χ : k ⟶ l) (ψ : l ⟶ m) (φ : m ⟶ n)
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O n).O)) :
    (S.transitionMorphism χ).pushforward.map
        ((S.componentModuleSheaf O l).map
          ((S.transitionPushforwardModulesCompIso O ψ φ).hom.app M)) =
      (S.transitionMorphism χ).pushforward.map
        ((S.pushforwardCompSymm ψ φ).hom.app ((S.componentModuleSheaf O n).obj M)) :=
  Functor.congr_map (S.transitionMorphism χ).pushforward
    (S.componentModuleSheaf_transitionPushforwardModulesCompIso_hom O ψ φ M)

/-- The cocycle law for the geometric compositors with the inner comparison written as the
underlying sheaf-of-sets map of the comparison of direct images of modules. -/
theorem pushforwardCompSymm_assoc_componentModuleSheaf' {k l m n : SimplexCategory} (χ : k ⟶ l)
    (ψ : l ⟶ m) (φ : m ⟶ n)
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O n).O)) :
    (S.pushforwardCompSymm χ ψ).hom.app
          ((S.componentModuleSheaf O m).obj ((S.transitionPushforwardModules O φ).obj M)) ≫
        (S.pushforwardCompSymm (χ ≫ ψ) φ).hom.app ((S.componentModuleSheaf O n).obj M) =
      (S.transitionMorphism χ).pushforward.map
          ((S.componentModuleSheaf O l).map
            ((S.transitionPushforwardModulesCompIso O ψ φ).hom.app M)) ≫
        (S.pushforwardCompSymm χ (ψ ≫ φ)).hom.app ((S.componentModuleSheaf O n).obj M) :=
  (S.pushforwardCompSymm_assoc_componentModuleSheaf O χ ψ φ M).trans
    (congrArg (fun t ↦ t ≫ (S.pushforwardCompSymm χ (ψ ≫ φ)).hom.app
      ((S.componentModuleSheaf O n).obj M))
      (S.transitionMorphism_map_componentModuleSheaf_compIso O χ ψ φ M).symm)

/-! ### Associativity of the compositor of direct images of sheaves of modules -/

/-- The underlying sheaf-of-sets map of the left-hand side of the cocycle law for the comparison
of direct images of sheaves of modules: comparing through `χ ≫ ψ`. -/
theorem componentModuleSheaf_transitionPushforwardModulesCompIso_comp_left
    {k l m n : SimplexCategory} (χ : k ⟶ l) (ψ : l ⟶ m) (φ : m ⟶ n)
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O n).O)) :
    (S.componentModuleSheaf O k).map
        ((S.transitionPushforwardModulesCompIso O χ ψ).hom.app
            ((S.transitionPushforwardModules O φ).obj M) ≫
          (S.transitionPushforwardModulesCompIso O (χ ≫ ψ) φ).hom.app M) =
      (S.pushforwardCompSymm χ ψ).hom.app
          ((S.componentModuleSheaf O m).obj ((S.transitionPushforwardModules O φ).obj M)) ≫
        (S.pushforwardCompSymm (χ ≫ ψ) φ).hom.app ((S.componentModuleSheaf O n).obj M) := by
  rw [CategoryTheory.Functor.map_comp,
    S.componentModuleSheaf_transitionPushforwardModulesCompIso_hom O χ ψ
      ((S.transitionPushforwardModules O φ).obj M),
    S.componentModuleSheaf_transitionPushforwardModulesCompIso_hom O (χ ≫ ψ) φ M]
  rfl

/-- The underlying sheaf-of-sets map of the right-hand side of the cocycle law for the
comparison of direct images of sheaves of modules: comparing through `ψ ≫ φ`. -/
theorem componentModuleSheaf_transitionPushforwardModulesCompIso_comp_right
    {k l m n : SimplexCategory} (χ : k ⟶ l) (ψ : l ⟶ m) (φ : m ⟶ n)
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O n).O)) :
    (S.componentModuleSheaf O k).map
        ((S.transitionPushforwardModules O χ).map
            ((S.transitionPushforwardModulesCompIso O ψ φ).hom.app M) ≫
          (S.transitionPushforwardModulesCompIso O χ (ψ ≫ φ)).hom.app M) =
      (S.transitionMorphism χ).pushforward.map
          ((S.componentModuleSheaf O l).map
            ((S.transitionPushforwardModulesCompIso O ψ φ).hom.app M)) ≫
        (S.pushforwardCompSymm χ (ψ ≫ φ)).hom.app ((S.componentModuleSheaf O n).obj M) := by
  rw [CategoryTheory.Functor.map_comp,
    S.componentModuleSheaf_transitionPushforwardModules_map O χ
      ((S.transitionPushforwardModulesCompIso O ψ φ).hom.app M),
    S.componentModuleSheaf_transitionPushforwardModulesCompIso_hom O χ (ψ ≫ φ) M]
  rfl

/-- **The cocycle law for the comparison of direct images of sheaves of modules**, read at a
sheaf of modules. It is the cocycle law of the geometric compositor of Stacks 09WE, a morphism
of sheaves of modules being determined by the underlying morphism of sheaves of sets. -/
theorem transitionPushforwardModulesCompIso_assoc_app {k l m n : SimplexCategory} (χ : k ⟶ l)
    (ψ : l ⟶ m) (φ : m ⟶ n)
    (M : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O n).O)) :
    (S.transitionPushforwardModulesCompIso O χ ψ).hom.app
          ((S.transitionPushforwardModules O φ).obj M) ≫
        (S.transitionPushforwardModulesCompIso O (χ ≫ ψ) φ).hom.app M =
      (S.transitionPushforwardModules O χ).map
          ((S.transitionPushforwardModulesCompIso O ψ φ).hom.app M) ≫
        (S.transitionPushforwardModulesCompIso O χ (ψ ≫ φ)).hom.app M :=
  S.componentModuleSheaf_hom_ext O
    ((S.componentModuleSheaf_transitionPushforwardModulesCompIso_comp_left O χ ψ φ M).trans
      ((S.pushforwardCompSymm_assoc_componentModuleSheaf' O χ ψ φ M).trans
        (S.componentModuleSheaf_transitionPushforwardModulesCompIso_comp_right O
          χ ψ φ M).symm))

/-- Transport of the direct image of sheaves of modules along an equality of simplex maps. -/
abbrev transitionPushforwardModulesCongr {m n : SimplexCategory} {φ₁ φ₂ : m ⟶ n}
    (h : φ₁ = φ₂) :
    S.transitionPushforwardModules O φ₁ ≅ S.transitionPushforwardModules O φ₂ :=
  eqToIso (congrArg (fun t ↦ S.transitionPushforwardModules O t) h)

/-- **The cocycle law for the comparison of direct images of sheaves of modules**, as an
equality of natural isomorphisms. This is the shape consumed by
`CategoryTheory.Adjunction.leftAdjointCompIso_assoc`; the transport along `Category.assoc χ ψ φ`
is carried because the two spellings of the triple composite are the same simplex map but not
the same term. -/
theorem transitionPushforwardModulesCompIso_assoc {k l m n : SimplexCategory} (χ : k ⟶ l)
    (ψ : l ⟶ m) (φ : m ⟶ n) :
    Functor.isoWhiskerLeft (S.transitionPushforwardModules O φ)
          (S.transitionPushforwardModulesCompIso O χ ψ) ≪≫
        S.transitionPushforwardModulesCompIso O (χ ≫ ψ) φ ≪≫
          S.transitionPushforwardModulesCongr O (Category.assoc χ ψ φ) =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (S.transitionPushforwardModulesCompIso O ψ φ)
            (S.transitionPushforwardModules O χ) ≪≫
          S.transitionPushforwardModulesCompIso O χ (ψ ≫ φ) := by
  refine Iso.ext (NatTrans.ext (funext fun M ↦ ?_))
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Iso.symm_hom, Functor.associator_inv_app, Category.id_comp]
  have hB : (S.transitionPushforwardModulesCompIso O (χ ≫ ψ) φ).hom.app M ≫
        (S.transitionPushforwardModulesCongr O (Category.assoc χ ψ φ)).hom.app M =
      (S.transitionPushforwardModulesCompIso O (χ ≫ ψ) φ).hom.app M := Category.comp_id _
  exact (congrArg (fun t ↦ (S.transitionPushforwardModulesCompIso O χ ψ).hom.app
      ((S.transitionPushforwardModules O φ).obj M) ≫ t) hB).trans
    (S.transitionPushforwardModulesCompIso_assoc_app O χ ψ φ M)

/-! ### Associativity of the compositor of pullbacks of sheaves of modules -/

/-- The adjunction of Stacks 03D7 between pullback and direct image of sheaves of modules along
the transition morphism of a simplex map, in the spelling that the comparison of pullbacks of
`CategoryTheory.SimplicialSiteSituation.transitionPullbackModulesCompIso` is built from. -/
abbrev transitionPullbackAdj {m n : SimplexCategory} (φ : m ⟶ n) :
    (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules ⊣
      S.transitionPushforwardModules O φ :=
  pullbackAdjPushforwardModules (S.transitionRingedToposHom O φ).toModulesHom

/-- Transport of the pullback of sheaves of modules along an equality of simplex maps. -/
abbrev transitionPullbackModulesCongr {m n : SimplexCategory} {φ₁ φ₂ : m ⟶ n} (h : φ₁ = φ₂) :
    (S.transitionRingedToposHom O φ₁).toModulesHom.pullbackModules ≅
      (S.transitionRingedToposHom O φ₂).toModulesHom.pullbackModules :=
  eqToIso (congrArg (fun t ↦ (S.transitionRingedToposHom O t).toModulesHom.pullbackModules) h)

/-- **The comparison of pullbacks of sheaves of modules is the adjoint mate of the comparison of
direct images.** Both are determined by their conjugate under the two adjunctions, and the two
conjugates agree. -/
theorem transitionPullbackModulesCompIso_eq_leftAdjointCompIso {l m n : SimplexCategory}
    (ψ : l ⟶ m) (φ : m ⟶ n) :
    S.transitionPullbackModulesCompIso O ψ φ =
      (Adjunction.leftAdjointCompIso (S.transitionPullbackAdj O ψ)
        (S.transitionPullbackAdj O φ) (S.transitionPullbackAdj O (ψ ≫ φ))
        (S.transitionPushforwardModulesCompIso O ψ φ)).symm := by
  refine Iso.ext ?_
  have h₁ : (S.transitionPullbackModulesCompIso O ψ φ).hom =
      (conjugateEquiv ((S.transitionPullbackAdj O ψ).comp (S.transitionPullbackAdj O φ))
        (S.transitionPullbackAdj O (ψ ≫ φ))).symm
        (S.transitionPushforwardModulesCompIso O ψ φ).hom :=
    Adjunction.leftAdjointUniq_ofNatIsoRight_hom _ _ _
  have h₂ := Adjunction.conjugateEquiv_leftAdjointCompIso_inv
    (S.transitionPullbackAdj O ψ) (S.transitionPullbackAdj O φ)
    (S.transitionPullbackAdj O (ψ ≫ φ)) (S.transitionPushforwardModulesCompIso O ψ φ)
  rw [h₁, Iso.symm_hom, ← h₂, Equiv.symm_apply_apply]

/-- **The cocycle law for the comparison of pullbacks of sheaves of modules.** It is the cocycle
law for the comparison of direct images, transported to the left adjoints by
`CategoryTheory.Adjunction.leftAdjointCompIso_assoc`. -/
theorem transitionPullbackModulesCompIso_assoc {k l m n : SimplexCategory} (χ : k ⟶ l)
    (ψ : l ⟶ m) (φ : m ⟶ n) :
    Functor.isoWhiskerLeft (S.transitionRingedToposHom O χ).toModulesHom.pullbackModules
          (S.transitionPullbackModulesCompIso O ψ φ).symm ≪≫
        (S.transitionPullbackModulesCompIso O χ (ψ ≫ φ)).symm =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (S.transitionPullbackModulesCompIso O χ ψ).symm
            (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules ≪≫
          ((S.transitionPullbackModulesCompIso O (χ ≫ ψ) φ).symm ≪≫
            S.transitionPullbackModulesCongr O (Category.assoc χ ψ φ)) := by
  rw [S.transitionPullbackModulesCompIso_eq_leftAdjointCompIso O ψ φ,
    S.transitionPullbackModulesCompIso_eq_leftAdjointCompIso O χ (ψ ≫ φ),
    S.transitionPullbackModulesCompIso_eq_leftAdjointCompIso O χ ψ,
    S.transitionPullbackModulesCompIso_eq_leftAdjointCompIso O (χ ≫ ψ) φ,
    Iso.symm_symm_eq, Iso.symm_symm_eq, Iso.symm_symm_eq, Iso.symm_symm_eq,
    Adjunction.leftAdjointCompIso_congr (fun α ↦ S.transitionPullbackAdj O α) _ _
      (Category.assoc χ ψ φ)]
  exact Adjunction.leftAdjointCompIso_assoc _ _ _ _ _ _ _ _ _ _
    (S.transitionPushforwardModulesCompIso_assoc O χ ψ φ)

/-- The cocycle law for the comparison of pullbacks of sheaves of modules, read at a sheaf of
modules, with the transport along `Category.assoc χ ψ φ` on the route through `χ ≫ ψ`. -/
theorem transitionPullbackModulesCompIso_inv_assoc_congr_app {k l m n : SimplexCategory}
    (χ : k ⟶ l) (ψ : l ⟶ m) (φ : m ⟶ n)
    (X : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O k).O)) :
    (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.map
          ((S.transitionPullbackModulesCompIso O χ ψ).symm.hom.app X) ≫
        ((S.transitionPullbackModulesCompIso O (χ ≫ ψ) φ).symm ≪≫
          S.transitionPullbackModulesCongr O (Category.assoc χ ψ φ)).hom.app X =
      (S.transitionPullbackModulesCompIso O ψ φ).symm.hom.app
          ((S.transitionRingedToposHom O χ).toModulesHom.pullbackModules.obj X) ≫
        (S.transitionPullbackModulesCompIso O χ (ψ ≫ φ)).symm.hom.app X := by
  have h := NatTrans.congr_app
    (congrArg Iso.hom (S.transitionPullbackModulesCompIso_assoc O χ ψ φ)) X
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Iso.symm_hom, Functor.associator_inv_app, Category.id_comp] at h ⊢
  exact h.symm

/-- The cocycle law for the comparison of pullbacks of sheaves of modules, read at a sheaf of
modules and in the direction of the compositor. -/
theorem transitionPullbackModulesCompIso_inv_assoc_app {k l m n : SimplexCategory} (χ : k ⟶ l)
    (ψ : l ⟶ m) (φ : m ⟶ n)
    (X : SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf (S.componentRingedTopos O k).O)) :
    (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.map
          ((S.transitionPullbackModulesCompIso O χ ψ).inv.app X) ≫
        (S.transitionPullbackModulesCompIso O (χ ≫ ψ) φ).inv.app X =
      (S.transitionPullbackModulesCompIso O ψ φ).inv.app
          ((S.transitionRingedToposHom O χ).toModulesHom.pullbackModules.obj X) ≫
        (S.transitionPullbackModulesCompIso O χ (ψ ≫ φ)).inv.app X := by
  have h := NatTrans.congr_app
    (congrArg Iso.hom (S.transitionPullbackModulesCompIso_assoc O χ ψ φ)) X
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Iso.symm_hom, Functor.associator_inv_app, Category.id_comp] at h
  have hB : (S.transitionPullbackModulesCompIso O (χ ≫ ψ) φ).inv.app X ≫
        (S.transitionPullbackModulesCongr O (Category.assoc χ ψ φ)).hom.app X =
      (S.transitionPullbackModulesCompIso O (χ ≫ ψ) φ).inv.app X := Category.comp_id _
  exact (congrArg (fun t ↦ (S.transitionRingedToposHom O φ).toModulesHom.pullbackModules.map
    ((S.transitionPullbackModulesCompIso O χ ψ).inv.app X) ≫ t) hB).symm.trans h.symm

/-! ### Associativity of the compositor on the unbounded homotopy categories -/

/-- Degreewise pullback of complexes of sheaves of modules along the transition morphism of a
simplex map, as a functor between the unbounded homotopy categories.

It is `Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy` of the transition morphism, and
it is an opaque `def` rather than an `abbrev` for the reason recorded in the implementation notes
of `StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/DerivedPullback.lean`: it stops
the unifier at the definition boundary instead of letting it descend through
`componentRingedTopos` on every instance argument. -/
def transitionPullbackHomotopy {m n : SimplexCategory} (φ : m ⟶ n) :=
  pullbackMapHomotopy.{u, u, u, u, u, u} (S.transitionRingedToposHom O φ)

/-- Degreewise pullback on the unbounded homotopy categories is additive. Stated as an instance
because `CategoryTheory.SimplicialSiteSituation.transitionPullbackHomotopy` is opaque. -/
instance transitionPullbackHomotopy_additive {m n : SimplexCategory} (φ : m ⟶ n) :
    (S.transitionPullbackHomotopy O φ).Additive :=
  inferInstanceAs
    (pullbackMapHomotopy.{u, u, u, u, u, u} (S.transitionRingedToposHom O φ)).Additive

/-- The compositor of degreewise pullbacks of complexes of sheaves of modules on the unbounded
homotopy categories: the comparison of pullbacks of sheaves of modules applied degreewise. It is
the third factor of
`CategoryTheory.SimplicialSiteSituation.derivedTransitionCompCounit`, and it is opaque for the
same reason as `CategoryTheory.SimplicialSiteSituation.transitionPullbackHomotopy`. -/
def transitionPullbackHomotopyComp {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :=
  (Functor.mapHomotopyCategoryCompIso (S.transitionPullbackModulesCompIso O ψ φ).symm
    (ComplexShape.up ℤ)).hom

/-- The opaque degreewise pullback on the unbounded homotopy categories is
`Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy` of the transition morphism. Recorded
so that statements written through the opaque name can be matched with the library's spelling by
rewriting rather than by unification. -/
theorem transitionPullbackHomotopy_eq {m n : SimplexCategory} (φ : m ⟶ n) :
    S.transitionPullbackHomotopy O φ =
      pullbackMapHomotopy.{u, u, u, u, u, u} (S.transitionRingedToposHom O φ) :=
  rfl

/-- The opaque compositor on the unbounded homotopy categories is the comparison of pullbacks of
sheaves of modules applied degreewise, which is the form
`CategoryTheory.SimplicialSiteSituation.derivedTransitionCompCounit_app` uses. -/
theorem transitionPullbackHomotopyComp_eq {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    S.transitionPullbackHomotopyComp O ψ φ =
      (Functor.mapHomotopyCategoryCompIso (S.transitionPullbackModulesCompIso O ψ φ).symm
        (ComplexShape.up ℤ)).hom :=
  rfl

/-- The opaque degreewise pullback on the unbounded homotopy categories acts on morphisms as
`Stacks.Cohomology.DerivedPushforward.pullbackMapHomotopy` does. -/
theorem transitionPullbackHomotopy_map {m n : SimplexCategory} (φ : m ⟶ n)
    {A B : HomotopyCategory (S.componentRingedTopos O m).Modules (ComplexShape.up ℤ)}
    (g : A ⟶ B) :
    (S.transitionPullbackHomotopy O φ).map g =
      (pullbackMapHomotopy.{u, u, u, u, u, u} (S.transitionRingedToposHom O φ)).map g :=
  rfl

/-- **The cocycle law for the compositor of degreewise pullbacks on the unbounded homotopy
categories.** It is the cocycle law for the comparison of pullbacks of sheaves of modules,
applied degreewise. No transport appears: composition in the simplex category is associative by
`rfl`, so the two spellings of the triple composite give the same degreewise pullback. -/
theorem transitionPullbackHomotopyComp_assoc {k l m n : SimplexCategory} (χ : k ⟶ l)
    (ψ : l ⟶ m) (φ : m ⟶ n) :
    Functor.whiskerRight (S.transitionPullbackHomotopyComp O χ ψ)
            (S.transitionPullbackHomotopy O φ) ≫
          S.transitionPullbackHomotopyComp O (χ ≫ ψ) φ =
      (Functor.associator _ _ _).hom ≫
        Functor.whiskerLeft (S.transitionPullbackHomotopy O χ)
            (S.transitionPullbackHomotopyComp O ψ φ) ≫
          S.transitionPullbackHomotopyComp O χ (ψ ≫ φ) :=
  mapHomotopyCategoryCompIso_hom_assoc _ _ _ _
    (fun X ↦ S.transitionPullbackModulesCompIso_inv_assoc_app O χ ψ φ X)

end CategoryTheory.SimplicialSiteSituation

end
