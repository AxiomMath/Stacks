module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.DerivedPullback
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianPair

/-!
# Pairs of modules with a cocycle isomorphism on a simplicial site

Let `S` be a simplicial-site situation and `O` a sheaf of commutative rings on its total site.
A pair `(F, α)` consists of an `O_0`-module `F` on the degree-zero component together with an
isomorphism `α : f_{δ¹₁}^* F ≅ f_{δ¹₀}^* F` of `O_1`-modules satisfying the cocycle condition
`f_{δ²₁}^* α = f_{δ²₀}^* α ∘ f_{δ²₂}^* α` of `O_2`-modules. These pairs form a category, the
morphisms being the morphisms of degree-zero modules commuting with the two isomorphisms.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.componentModulePullback`: the pullback `f_φ^*` of
  sheaves of modules along the transition morphism of ringed topoi of a simplex map.
* `CategoryTheory.SimplicialSiteSituation.pasteModules`: the canonical identification
  `f_φ^* f_ψ^* F ≅ f_{ψ ≫ φ}^* F`, the pullback compositor read at one module.
* `CategoryTheory.SimplicialSiteSituation.glueModulesOfEq`: the identification of the pullbacks
  of a module along two factorizations of one simplex map.
* `CategoryTheory.SimplicialSiteSituation.IsModuleCocycle`: the cocycle condition in degree two.
* `CategoryTheory.SimplicialSiteSituation.CartesianModulePair`: the category of pairs `(F, α)`.

## Main results

* `CategoryTheory.SimplicialSiteSituation.CartesianModulePair.isoMk`: an isomorphism of
  degree-zero modules commuting with the comparison isomorphisms is an isomorphism of pairs.

## Implementation notes

The identifications in the cocycle condition are not chosen: each is the pullback compositor
`CategoryTheory.SimplicialSiteSituation.transitionPullbackModulesCompIso`, which is itself
pinned as the adjoint mate of the comparison of direct images, transported along one of the
three simplicial identities `δ¹₁ ≫ δ²₂ = δ¹₁ ≫ δ²₁`, `δ¹₀ ≫ δ²₂ = δ¹₁ ≫ δ²₀` and
`δ¹₀ ≫ δ²₀ = δ¹₀ ≫ δ²₁`, each read as a factorization through a vertex of `⦋2⦌`. This mirrors
`CategoryTheory.SimplicialSiteSituation.CartesianPair` for sheaves of sets, with the inverse
image of sheaves replaced by the pullback of sheaves of modules.

`componentModulePullback` is an opaque `def` rather than an `abbrev`, and the cocycle
condition is a named predicate rather than a field written out inside the structure: with
the pullback of modules spelled out and the equation inline, checking the structure
declaration exhausts the kernel, because the four layers of
`Stacks.Sheaves.RingedToposModules.pullbackModules` are unfolded while the domains and
codomains of the five factors are matched; behind the two definition boundaries the same
declaration elaborates and kernel-checks in seconds.

The structure sheaf is a sheaf of *commutative* rings, which is the level at which this
development has ringed topoi, their morphisms and the pullback of modules.

## References

* [Stacks Project, Tag 07TH](https://stacks.math.columbia.edu/tag/07TH)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

/-! ### The pullback compositor at a module -/

/-- The pullback `f_φ^*` of sheaves of modules along the morphism of ringed topoi induced by a
simplex map `φ : m ⟶ n`. -/
noncomputable def componentModulePullback {m n : SimplexCategory} (φ : m ⟶ n) :
    (S.componentRingedTopos O m).Modules ⥤ (S.componentRingedTopos O n).Modules :=
  ((S.transitionRingedToposHom O φ).toModulesHom.pullbackModules)

/-- The canonical identification `f_φ^* f_ψ^* F ≅ f_{ψ ≫ φ}^* F` of pullbacks of a module along
the transition morphisms of a composable pair of simplex maps. -/
noncomputable def pasteModules {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (F : (S.componentRingedTopos O l).Modules) :
    (S.componentModulePullback O φ).obj ((S.componentModulePullback O ψ).obj F) ≅
      (S.componentModulePullback O (ψ ≫ φ)).obj F :=
  ((S.transitionPullbackModulesCompIso O ψ φ).app F).symm

/-- The pullback compositor at a factorization `ψ ≫ φ = θ` of a simplex map: the identification
`f_φ^* f_ψ^* F ≅ f_θ^* F`. -/
noncomputable def pasteModulesOfEq {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (θ : l ⟶ n) (h : ψ ≫ φ = θ) (F : (S.componentRingedTopos O l).Modules) :
    (S.componentModulePullback O φ).obj ((S.componentModulePullback O ψ).obj F) ≅
      (S.componentModulePullback O θ).obj F :=
  S.pasteModules O ψ φ F ≪≫
    eqToIso (congrArg (fun k => (S.componentModulePullback O k).obj F) h)

/-- The identification of the pullbacks of a module along two factorizations `ψ ≫ φ` and
`ψ' ≫ φ'` of one simplex map, built from the pullback compositor at each. -/
noncomputable def glueModulesOfEq {l m n : SimplexCategory} (ψ ψ' : l ⟶ m) (φ φ' : m ⟶ n)
    (v : l ⟶ n) (h : ψ ≫ φ = v) (h' : ψ' ≫ φ' = v)
    (F : (S.componentRingedTopos O l).Modules) :
    (S.componentModulePullback O φ).obj ((S.componentModulePullback O ψ).obj F) ≅
      (S.componentModulePullback O φ').obj ((S.componentModulePullback O ψ').obj F) :=
  S.pasteModulesOfEq O ψ φ v h F ≪≫ (S.pasteModulesOfEq O ψ' φ' v h' F).symm

/-- The identification of two factorizations, written out. -/
theorem glueModulesOfEq_hom {l m n : SimplexCategory} (ψ ψ' : l ⟶ m) (φ φ' : m ⟶ n)
    (v : l ⟶ n) (h : ψ ≫ φ = v) (h' : ψ' ≫ φ' = v)
    (F : (S.componentRingedTopos O l).Modules) :
    (S.glueModulesOfEq O ψ ψ' φ φ' v h h' F).hom =
      (S.pasteModulesOfEq O ψ φ v h F).hom ≫ (S.pasteModulesOfEq O ψ' φ' v h' F).inv := rfl

/-- The inverse of the identification of two factorizations, written out. -/
theorem glueModulesOfEq_inv {l m n : SimplexCategory} (ψ ψ' : l ⟶ m) (φ φ' : m ⟶ n)
    (v : l ⟶ n) (h : ψ ≫ φ = v) (h' : ψ' ≫ φ' = v)
    (F : (S.componentRingedTopos O l).Modules) :
    (S.glueModulesOfEq O ψ ψ' φ φ' v h h' F).inv =
      (S.pasteModulesOfEq O ψ' φ' v h' F).hom ≫ (S.pasteModulesOfEq O ψ φ v h F).inv := rfl

/-! ### The three identifications occurring in the cocycle condition -/

/-- The identification of the two pullbacks of `f_{δ¹₁}^* F` to degree two occurring in the
cocycle condition, along `δ¹₁ ≫ δ²₂ = δ¹₁ ≫ δ²₁`. -/
noncomputable def glueModulesLeft (F : (S.componentRingedTopos O ⦋0⦌).Modules) :
    (S.componentModulePullback O (SimplexCategory.δ (2 : Fin 3))).obj
        ((S.componentModulePullback O (SimplexCategory.δ (1 : Fin 2))).obj F) ≅
      (S.componentModulePullback O (SimplexCategory.δ (1 : Fin 3))).obj
        ((S.componentModulePullback O (SimplexCategory.δ (1 : Fin 2))).obj F) :=
  S.glueModulesOfEq O _ _ _ _ _ SimplexCategory.delta_one_comp_delta_two
    SimplexCategory.delta_one_comp_delta_one F

/-- The identification of `f_{δ²₂}^* f_{δ¹₀}^* F` with `f_{δ²₀}^* f_{δ¹₁}^* F`, along
`δ¹₀ ≫ δ²₂ = δ¹₁ ≫ δ²₀`. -/
noncomputable def glueModulesMiddle (F : (S.componentRingedTopos O ⦋0⦌).Modules) :
    (S.componentModulePullback O (SimplexCategory.δ (2 : Fin 3))).obj
        ((S.componentModulePullback O (SimplexCategory.δ (0 : Fin 2))).obj F) ≅
      (S.componentModulePullback O (SimplexCategory.δ (0 : Fin 3))).obj
        ((S.componentModulePullback O (SimplexCategory.δ (1 : Fin 2))).obj F) :=
  S.glueModulesOfEq O _ _ _ _ _ SimplexCategory.delta_zero_comp_delta_two
    SimplexCategory.delta_one_comp_delta_zero F

/-- The identification of the two pullbacks of `f_{δ¹₀}^* F` to degree two occurring in the
cocycle condition, along `δ¹₀ ≫ δ²₀ = δ¹₀ ≫ δ²₁`. -/
noncomputable def glueModulesRight (F : (S.componentRingedTopos O ⦋0⦌).Modules) :
    (S.componentModulePullback O (SimplexCategory.δ (0 : Fin 3))).obj
        ((S.componentModulePullback O (SimplexCategory.δ (0 : Fin 2))).obj F) ≅
      (S.componentModulePullback O (SimplexCategory.δ (1 : Fin 3))).obj
        ((S.componentModulePullback O (SimplexCategory.δ (0 : Fin 2))).obj F) :=
  S.glueModulesOfEq O _ _ _ _ _ SimplexCategory.delta_zero_comp_delta_zero
    SimplexCategory.delta_zero_comp_delta_one F

/-! ### The category of pairs -/

/-- The cocycle condition `f_{δ²₁}^* α = f_{δ²₀}^* α ∘ f_{δ²₂}^* α` in degree two on an
isomorphism `α : f_{δ¹₁}^* F ≅ f_{δ¹₀}^* F` of modules on the degree-one component, the three
pullbacks being compared by the canonical identifications of the pullback compositor. -/
noncomputable def IsModuleCocycle (F : (S.componentRingedTopos O ⦋0⦌).Modules)
    (α : (S.componentModulePullback O (SimplexCategory.δ (1 : Fin 2))).obj F ≅
      (S.componentModulePullback O (SimplexCategory.δ (0 : Fin 2))).obj F) : Prop :=
  (S.componentModulePullback O (SimplexCategory.δ (1 : Fin 3))).map α.hom =
    (S.glueModulesLeft O F).inv ≫
      (S.componentModulePullback O (SimplexCategory.δ (2 : Fin 3))).map α.hom ≫
      (S.glueModulesMiddle O F).hom ≫
      (S.componentModulePullback O (SimplexCategory.δ (0 : Fin 3))).map α.hom ≫
      (S.glueModulesRight O F).hom

/-- A pair `(F, α)`: a module over the structure sheaf of the degree-zero component of a
simplicial-site situation together with an isomorphism `α : f_{δ¹₁}^* F ≅ f_{δ¹₀}^* F` of
modules on the degree-one component satisfying the cocycle condition
`f_{δ²₁}^* α = f_{δ²₀}^* α ∘ f_{δ²₂}^* α` on the degree-two component. -/
structure CartesianModulePair (S : SimplicialSiteSituation.{u})
    (O : Sheaf S.totalTopology CommRingCat.{u}) where
  /-- The module on the degree-zero component. -/
  module : (S.componentRingedTopos O ⦋0⦌).Modules
  /-- The comparison isomorphism between the two pullbacks to degree one. -/
  iso : (S.componentModulePullback O (SimplexCategory.δ (1 : Fin 2))).obj module ≅
    (S.componentModulePullback O (SimplexCategory.δ (0 : Fin 2))).obj module
  /-- The cocycle condition on the degree-two component. -/
  cocycle : S.IsModuleCocycle O module iso

namespace CartesianModulePair

/-- A morphism of pairs is a morphism of the degree-zero modules commuting with the comparison
isomorphisms. -/
structure Hom (A B : CartesianModulePair S O) where
  /-- The morphism of the degree-zero modules. -/
  map : A.module ⟶ B.module
  /-- Compatibility with the comparison isomorphisms. -/
  comm : (S.componentModulePullback O (SimplexCategory.δ (1 : Fin 2))).map map ≫ B.iso.hom =
    A.iso.hom ≫ (S.componentModulePullback O (SimplexCategory.δ (0 : Fin 2))).map map

/-- Pairs form a category, with composition that of the morphisms of degree-zero modules. -/
noncomputable instance : Category (CartesianModulePair S O) where
  Hom A B := Hom S O A B
  id A := { map := 𝟙 A.module, comm := by simp }
  comp f g :=
    { map := f.map ≫ g.map
      comm := by
        simp only [Functor.map_comp, Category.assoc, g.comm, reassoc_of% f.comm] }

/-- The identity morphism of pairs is the identity of the degree-zero module. -/
@[simp] theorem id_map (A : CartesianModulePair S O) : Hom.map (𝟙 A) = 𝟙 A.module := rfl

/-- Composition of morphisms of pairs composes the morphisms of degree-zero modules. -/
@[simp] theorem comp_map {A B C : CartesianModulePair S O} (f : A ⟶ B) (g : B ⟶ C) :
    (f ≫ g).map = f.map ≫ g.map := rfl

/-- A morphism of pairs is determined by its morphism of degree-zero modules. -/
theorem hom_ext {A B : CartesianModulePair S O} {f g : A ⟶ B} (h : f.map = g.map) : f = g := by
  obtain ⟨f, hf⟩ := f
  obtain ⟨g, hg⟩ := g
  subst h
  rfl

/-- An isomorphism of degree-zero modules compatible with the comparison isomorphisms is an
isomorphism of pairs. -/
noncomputable def isoMk {A B : CartesianModulePair S O} (e : A.module ≅ B.module)
    (h : (S.componentModulePullback O (SimplexCategory.δ (1 : Fin 2))).map e.hom ≫ B.iso.hom =
      A.iso.hom ≫
        (S.componentModulePullback O (SimplexCategory.δ (0 : Fin 2))).map e.hom) :
    A ≅ B where
  hom := ⟨e.hom, h⟩
  inv :=
    ⟨e.inv, by
      rw [← cancel_epi ((S.componentModulePullback O
          (SimplexCategory.δ (1 : Fin 2))).map e.hom), reassoc_of% h]
      simp only [← Functor.map_comp_assoc, ← Functor.map_comp, e.hom_inv_id,
        CategoryTheory.Functor.map_id, Category.id_comp, Category.comp_id]⟩
  hom_inv_id := hom_ext S O (by simp)
  inv_hom_id := hom_ext S O (by simp)

end CartesianModulePair

end CategoryTheory.SimplicialSiteSituation

end
