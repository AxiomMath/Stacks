module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CartesianModulePair
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleTransitionCocycle
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CartesianPairFunctor

/-!
# The pair attached to a cartesian module on a simplicial site

Let `S` be a simplicial-site situation and `O` a sheaf of commutative rings on its total site.
A cartesian sheaf of `O`-modules `M` has a degree-zero restriction `M₀` and an invertible
transition `f_{δ¹ₖ}^*M₀ ⟶ M₁` for each of the two faces `δ¹ₖ`; comparing the two gives an
isomorphism `α : f_{δ¹₁}^*M₀ ≅ f_{δ¹₀}^*M₀` of modules on the degree-one component satisfying
the cocycle condition in degree two, so `M` determines a
`CategoryTheory.SimplicialSiteSituation.CartesianModulePair`. This file builds that functor and
shows it is faithful. Fullness, essential surjectivity and the resulting equivalence of
Stacks 07TH, `CategoryTheory.SimplicialSiteSituation.cartesianModuleSheafEquivCartesianModulePair`,
are in
`StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CartesianModulePairEquivalence`.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.componentModule`,
  `.componentModuleMap` and `.componentTransition`: the restriction of a module on the total site
  to a component, of a morphism of such modules, and the transition of Stacks 09WF, all read
  between modules of the component ringed topoi.
* `CategoryTheory.SimplicialSiteSituation.CartesianModuleSheaf`: the category of cartesian
  sheaves of `O`-modules on the total site, as a full subcategory.
* `CategoryTheory.SimplicialSiteSituation.componentTransitionIso`: the transition of a cartesian
  module, as an isomorphism.
* `CategoryTheory.SimplicialSiteSituation.cartesianModuleIso`: the comparison `α` of a cartesian
  module.
* `CategoryTheory.SimplicialSiteSituation.faceSquareTransitionModulesIso`: the composite of the
  transitions of a cartesian module along a vertex of `⦋p⦌` and a simplex map out of `⦋p⦌`; for
  the two faces it is the composite `f_{δ²ⱼ}^*f_{δ¹ᵢ}^*M₀ ≅ M₂`.
* `CategoryTheory.SimplicialSiteSituation.cartesianModulePairFunctor`: the functor of
  Stacks 07TH from cartesian modules to pairs.

## Main results

* `CategoryTheory.SimplicialSiteSituation.fiberTransitionModules_naturality`: the transition of
  component modules is natural in the module.
* `CategoryTheory.SimplicialSiteSituation.cartesianModuleIso_cocycle`: the comparison of a
  cartesian module satisfies the cocycle condition of Stacks 07TH.
* `CategoryTheory.SimplicialSiteSituation.cartesianModuleIso_hom_comp`: the comparison is pinned
  by its composite with the transition for `δ¹₀`, so the functor is not an abstract choice.
* `CategoryTheory.SimplicialSiteSituation.totalModule_hom_ext`: a morphism of sheaves of modules
  on the total site is determined by its restrictions to the components.
* `CategoryTheory.SimplicialSiteSituation.cartesianModulePairFunctor_faithful`: the functor to
  pairs is faithful.

## Implementation notes

The source proves Stacks 07TH by reference to Stacks 0D7I, the same statement for sheaves of
sets, `CategoryTheory.SimplicialSiteSituation.cartesianSheafEquivCartesianPair`. That proof does
not transfer to modules verbatim, because the pullback of modules is not the inverse image of the
underlying sheaves of sets but extension of scalars along it; the descent of a pair to a module
on the total site is therefore carried out at the level of modules in
`StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleDescentSystem`, and this
file provides only the functor and its faithfulness.

The three identifications occurring in the cocycle condition are carried to the composites
`faceSquareTransitionModulesIso` of the transitions along two faces by
`glueModulesOfEq_comp_componentTransition`, whose content is the cocycle law
`CategoryTheory.SimplicialSiteSituation.fiberTransitionModules_comp` of Stacks 09WF for modules.

A face `δ²ⱼ` has domain `⦋1⦌` while the composite of two faces has middle degree `⦋0 + 1⦌`, so
the degree of a component occurs in two spellings that differ by an invisible numeral, and a
pullback functor of modules read at the one is not syntactically the functor read at the other.
Each statement here therefore fixes the middle degree once, from the vertex rather than from the
face, and the two readings are reconciled only in the three `rfl`-equations
`glueModulesLeft_eq`, `glueModulesMiddle_eq` and `glueModulesRight_eq`, which say that the
identifications of the cocycle condition are the pullback compositors at the factorizations of
the vertices of `⦋2⦌`. The cocycle condition is then proved at that spelling and transported
with those three equations; asking a single `rfl` to reconcile the two spellings inside a
composite of pullback functors of modules exhausts the kernel instead.

Naturality of the transition in the module, which the definition does not record because
the transition is given one module at a time, is one transposition of the adjunction away from
naturality of the direct-image transition, and that is naturality of
`CategoryTheory.SimplicialSiteSituation.restrictTransition` read on sections.

Faithfulness descends to the underlying sheaves of sets, where it is `total_hom_ext` of
Stacks 09WF, together with the fact that for a cartesian module the transition along the last
vertex of `⦋n⦌` is invertible, so the restriction in degree `n` is determined by the restriction
in degree zero.

Two spellings of the modules on a component occur: `SheafOfModules` over the restriction of the
sheaf of rings, which is what the transition of Stacks 09WF is stated over, and the modules of
the component ringed topos, which is what the pullback of modules and hence the category of
pairs is stated over. They are equal by `rfl`, but not at reducible transparency, so a goal
mixing the two is not type-correct at the transparency `rw` uses and no rewriting is possible in
it. Everything here is therefore phrased in the second spelling alone, through
`componentModule`, `componentModuleMap` and `componentTransition`, which are opaque `def`s whose
declared types use it; the equation `componentTransitionIso_hom` is the one place the two meet.
For the same reason invertibility is never looked up by instance search: every transition of a
cartesian module is packaged once as `componentTransitionIso`, and the cancellations are
`CategoryTheory.Iso.cancel_iso_hom_left` and `.cancel_iso_hom_right` rather than `cancel_epi`
and `cancel_mono`.

The structure sheaf is a sheaf of *commutative* rings, which is the level at which this
development has ringed topoi, their morphisms and the pullback of modules, where the source says
"sheaf of rings".

## References

* [Stacks Project, Tag 07TH](https://stacks.math.columbia.edu/tag/07TH)
* [Stacks Project, Tag 0D7I](https://stacks.math.columbia.edu/tag/0D7I)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Sheaves.RingedToposModules
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSiteSituation

variable (S : SimplicialSiteSituation.{u}) (O : Sheaf S.totalTopology CommRingCat.{u})

/-! ### Restriction to a component, read in the component ringed topos -/

/-- The restriction of a sheaf of `O`-modules on the total site to the degree-`n` component, read
as a module of the component ringed topos of degree `n`. -/
noncomputable def componentModule (M : SheafOfModules.{u} (S.totalRingSheaf O))
    (n : SimplexCategory) : (S.componentRingedTopos O n).Modules :=
  (S.componentModuleRestriction (S.totalRingSheaf O) n).obj M

/-- The restriction of a morphism of sheaves of `O`-modules on the total site to the degree-`n`
component, read between modules of the component ringed topos of degree `n`. -/
noncomputable def componentModuleMap {M N : SheafOfModules.{u} (S.totalRingSheaf O)} (f : M ⟶ N)
    (n : SimplexCategory) : S.componentModule O M n ⟶ S.componentModule O N n :=
  (S.componentModuleRestriction (S.totalRingSheaf O) n).map f

/-- Restriction to a component carries an identity to an identity. -/
@[simp] theorem componentModuleMap_id (M : SheafOfModules.{u} (S.totalRingSheaf O))
    (n : SimplexCategory) :
    S.componentModuleMap O (𝟙 M) n = 𝟙 (S.componentModule O M n) :=
  (S.componentModuleRestriction (S.totalRingSheaf O) n).map_id M

/-- Restriction to a component carries a composite to the composite. -/
@[simp] theorem componentModuleMap_comp {M N P : SheafOfModules.{u} (S.totalRingSheaf O)}
    (f : M ⟶ N) (g : N ⟶ P) (n : SimplexCategory) :
    S.componentModuleMap O (f ≫ g) n =
      S.componentModuleMap O f n ≫ S.componentModuleMap O g n :=
  (S.componentModuleRestriction (S.totalRingSheaf O) n).map_comp f g

/-- **Stacks 09WF** for sheaves of modules: the transition `f_φ^*Mₘ ⟶ Mₙ` between the
restrictions of a sheaf of `O`-modules to the components of degrees `m` and `n`, read between
modules of the component ringed topoi. -/
noncomputable def componentTransition (M : SheafOfModules.{u} (S.totalRingSheaf O))
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (S.componentModulePullback O φ).obj (S.componentModule O M m) ⟶
      S.componentModule O M n :=
  S.fiberTransitionModules O φ M

/-! ### Naturality of the transition of component modules -/

/-- The direct-image transition of component modules is natural in the module: on sections it is
naturality of the direct-image transition of sheaves of sets. -/
theorem restrictTransitionModulesApp_naturality {m n : SimplexCategory} (φ : m ⟶ n)
    {M N : SheafOfModules.{u} (S.totalRingSheaf O)} (f : M ⟶ N) :
    (S.componentModuleRestriction (S.totalRingSheaf O) m).map f ≫
        S.restrictTransitionModulesApp O φ N =
      S.restrictTransitionModulesApp O φ M ≫
        (S.transitionRingedToposHom O φ).pushforwardModules.map
          ((S.componentModuleRestriction (S.totalRingSheaf O) n).map f) := by
  refine SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun V =>
    ModuleCat.hom_ext (LinearMap.ext fun x => ?_))
  exact congrArg (fun t => (Sheaf.sectionsFunctor (S.componentTopology m) V).map t x)
    ((S.restrictTransition φ).naturality
      ((Sheaf.moduleSheafFunctor (S.totalRingSheaf O)).map f))

/-- The transition `f_φ^*ℱₘ ⟶ ℱₙ` of component modules is natural in the sheaf of modules on the
total site. -/
theorem fiberTransitionModules_naturality {m n : SimplexCategory} (φ : m ⟶ n)
    {M N : SheafOfModules.{u} (S.totalRingSheaf O)} (f : M ⟶ N) :
    (S.componentModulePullback O φ).map
          ((S.componentModuleRestriction (S.totalRingSheaf O) m).map f) ≫
        S.fiberTransitionModules O φ N =
      S.fiberTransitionModules O φ M ≫
        (S.componentModuleRestriction (S.totalRingSheaf O) n).map f :=
  Adjunction.homEquiv_naturality_right_square
    (S.transitionRingedToposHom O φ).pullbackAdjPushforwardModules
    ((S.componentModuleRestriction (S.totalRingSheaf O) m).map f)
    (S.restrictTransitionModulesApp O φ N) (S.restrictTransitionModulesApp O φ M)
    ((S.componentModuleRestriction (S.totalRingSheaf O) n).map f)
    (S.restrictTransitionModulesApp_naturality O φ f)

/-- Naturality of the transition of component modules, read between modules of the component
ringed topoi. -/
theorem componentTransition_naturality {m n : SimplexCategory} (φ : m ⟶ n)
    {M N : SheafOfModules.{u} (S.totalRingSheaf O)} (f : M ⟶ N) :
    (S.componentModulePullback O φ).map (S.componentModuleMap O f m) ≫
        S.componentTransition O N φ =
      S.componentTransition O M φ ≫ S.componentModuleMap O f n :=
  S.fiberTransitionModules_naturality O φ f

/-! ### The compositor and the transitions of a module on the total site -/

/-- The cocycle law of Stacks 09WF, read between modules of the component ringed topoi. -/
theorem componentTransition_comp (M : SheafOfModules.{u} (S.totalRingSheaf O))
    {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    S.componentTransition O M (ψ ≫ φ) =
      (S.transitionPullbackModulesCompIso O ψ φ).hom.app (S.componentModule O M l) ≫
        (S.componentModulePullback O φ).map (S.componentTransition O M ψ) ≫
          S.componentTransition O M φ :=
  S.fiberTransitionModules_comp O ψ φ M

/-- The pullback compositor carries the composite of two transitions of a module on the total
site to the transition of the composite simplex map. -/
theorem pasteModules_comp_componentTransition (M : SheafOfModules.{u} (S.totalRingSheaf O))
    {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n) :
    (S.pasteModules O ψ φ (S.componentModule O M l)).hom ≫
        S.componentTransition O M (ψ ≫ φ) =
      (S.componentModulePullback O φ).map (S.componentTransition O M ψ) ≫
        S.componentTransition O M φ :=
  Eq.trans (congrArg (fun t => (S.pasteModules O ψ φ (S.componentModule O M l)).hom ≫ t)
      (S.componentTransition_comp O M ψ φ))
    (((S.transitionPullbackModulesCompIso O ψ φ).app
      (S.componentModule O M l)).inv_hom_id_assoc _)

/-- The transitions of a module on the total site are compatible with transport along an equality
of simplex maps. -/
theorem eqToHom_comp_componentTransition (M : SheafOfModules.{u} (S.totalRingSheaf O))
    {m n : SimplexCategory} {φ ψ : m ⟶ n} (h : φ = ψ) :
    eqToHom (congrArg (fun k => (S.componentModulePullback O k).obj (S.componentModule O M m))
          h) ≫ S.componentTransition O M ψ =
      S.componentTransition O M φ := by
  subst h
  exact Category.id_comp _

/-- At the tautological factorization the compositor of a factorization is the pullback
compositor. -/
private theorem pasteModulesOfEq_hom_rfl {l m n : SimplexCategory} (ψ : l ⟶ m) (φ : m ⟶ n)
    (F : (S.componentRingedTopos O l).Modules) :
    (S.pasteModulesOfEq O ψ φ (ψ ≫ φ) rfl F).hom = (S.pasteModules O ψ φ F).hom := by
  simp [pasteModulesOfEq]

/-- The compositor at a factorization carries the composite of two transitions of a module on the
total site to the transition of the factored map. -/
theorem pasteModulesOfEq_comp_componentTransition
    (M : SheafOfModules.{u} (S.totalRingSheaf O)) {l m n : SimplexCategory} (ψ : l ⟶ m)
    (φ : m ⟶ n) (θ : l ⟶ n) (h : ψ ≫ φ = θ) :
    (S.pasteModulesOfEq O ψ φ θ h (S.componentModule O M l)).hom ≫
        S.componentTransition O M θ =
      (S.componentModulePullback O φ).map (S.componentTransition O M ψ) ≫
        S.componentTransition O M φ := by
  subst h
  rw [S.pasteModulesOfEq_hom_rfl O ψ φ (S.componentModule O M l)]
  exact S.pasteModules_comp_componentTransition O M ψ φ

/-- The two composites of transitions attached to two factorizations of one simplex map agree
under the identification `glueModulesOfEq`. -/
theorem glueModulesOfEq_comp_componentTransition
    (M : SheafOfModules.{u} (S.totalRingSheaf O)) {l m n : SimplexCategory} (ψ ψ' : l ⟶ m)
    (φ φ' : m ⟶ n) (v : l ⟶ n) (h : ψ ≫ φ = v) (h' : ψ' ≫ φ' = v) :
    (S.glueModulesOfEq O ψ ψ' φ φ' v h h' (S.componentModule O M l)).hom ≫
        ((S.componentModulePullback O φ').map (S.componentTransition O M ψ') ≫
          S.componentTransition O M φ') =
      (S.componentModulePullback O φ).map (S.componentTransition O M ψ) ≫
        S.componentTransition O M φ := by
  have key : (S.pasteModulesOfEq O ψ' φ' v h' (S.componentModule O M l)).inv ≫
      ((S.componentModulePullback O φ').map (S.componentTransition O M ψ') ≫
        S.componentTransition O M φ') = S.componentTransition O M v :=
    (Iso.inv_comp_eq _).2 (S.pasteModulesOfEq_comp_componentTransition O M ψ' φ' v h').symm
  rw [S.glueModulesOfEq_hom O ψ ψ' φ φ' v h h', Category.assoc, key,
    S.pasteModulesOfEq_comp_componentTransition O M ψ φ v h]

/-! ### The pair attached to a cartesian module -/

/-- The category of cartesian sheaves of `O`-modules on the total site of a simplicial-site
situation. -/
abbrev CartesianModuleSheaf (S : SimplicialSiteSituation.{u})
    (O : Sheaf S.totalTopology CommRingCat.{u}) :=
  ObjectProperty.FullSubcategory (S.IsCartesianModule O)

/-- The transition `f_φ^*Mₘ ⟶ Mₙ` of a cartesian module, as an isomorphism of modules of the
component ringed topos of degree `n`. -/
noncomputable def componentTransitionIso (M : S.CartesianModuleSheaf O)
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (S.componentModulePullback O φ).obj (S.componentModule O M.obj m) ≅
      S.componentModule O M.obj n :=
  @asIso _ _ _ _ (S.componentTransition O M.obj φ) (M.property φ)

/-- The morphism underlying the transition isomorphism of a cartesian module is the transition of
Stacks 09WF. -/
theorem componentTransitionIso_hom (M : S.CartesianModuleSheaf O) {m n : SimplexCategory}
    (φ : m ⟶ n) :
    (S.componentTransitionIso O M φ).hom = S.fiberTransitionModules O φ M.obj := rfl

/-- The transition isomorphisms of cartesian modules are natural in the cartesian module. -/
theorem componentTransitionIso_naturality {M N : S.CartesianModuleSheaf O} (f : M ⟶ N)
    {m n : SimplexCategory} (φ : m ⟶ n) :
    (S.componentModulePullback O φ).map (S.componentModuleMap O f.hom m) ≫
        (S.componentTransitionIso O N φ).hom =
      (S.componentTransitionIso O M φ).hom ≫ S.componentModuleMap O f.hom n :=
  S.componentTransition_naturality O φ f.hom

/-- For a cartesian module, the comparison isomorphism `f_{δ¹₁}^*M₀ ≅ f_{δ¹₀}^*M₀` obtained from
the two transitions to degree one. -/
noncomputable def cartesianModuleIso (M : S.CartesianModuleSheaf O) :
    (S.componentModulePullback O (SimplexCategory.δ (1 : Fin 2))).obj
        (S.componentModule O M.obj ⦋0⦌) ≅
      (S.componentModulePullback O (SimplexCategory.δ (0 : Fin 2))).obj
        (S.componentModule O M.obj ⦋0⦌) :=
  S.componentTransitionIso O M (SimplexCategory.δ (1 : Fin 2)) ≪≫
    (S.componentTransitionIso O M (SimplexCategory.δ (0 : Fin 2))).symm

/-- The comparison isomorphism of a cartesian module composed with the transition for `δ¹₀` is
the transition for `δ¹₁`. -/
theorem cartesianModuleIso_hom_comp (M : S.CartesianModuleSheaf O) :
    (S.cartesianModuleIso O M).hom ≫
        (S.componentTransitionIso O M (SimplexCategory.δ (0 : Fin 2))).hom =
      (S.componentTransitionIso O M (SimplexCategory.δ (1 : Fin 2))).hom := by
  simp only [cartesianModuleIso, Iso.trans_hom, Iso.symm_hom, Category.assoc, Iso.inv_hom_id,
    Category.comp_id]

/-- The composite `f_φ^*f_ψ^*M₀ ≅ M_q` of the transitions of a cartesian module along a vertex
`ψ` of `⦋p⦌` and a simplex map `φ : ⦋p⦌ ⟶ ⦋q⦌`. For the two faces it is the composite
`f_{δ²ⱼ}^*f_{δ¹ᵢ}^*M₀ ≅ M₂`. -/
noncomputable def faceSquareTransitionModulesIso (M : S.CartesianModuleSheaf O)
    {p q : SimplexCategory} (ψ : ⦋0⦌ ⟶ p) (φ : p ⟶ q) :
    (S.componentModulePullback O φ).obj
        ((S.componentModulePullback O ψ).obj (S.componentModule O M.obj ⦋0⦌)) ≅
      S.componentModule O M.obj q :=
  (S.componentModulePullback O φ).mapIso (S.componentTransitionIso O M ψ) ≪≫
    S.componentTransitionIso O M φ

/-- The composite of the transitions of a cartesian module along two simplex maps, written
out. -/
theorem faceSquareTransitionModulesIso_hom (M : S.CartesianModuleSheaf O)
    {p q : SimplexCategory} (ψ : ⦋0⦌ ⟶ p) (φ : p ⟶ q) :
    (S.faceSquareTransitionModulesIso O M ψ φ).hom =
      (S.componentModulePullback O φ).map (S.componentTransition O M.obj ψ) ≫
        S.componentTransition O M.obj φ := rfl

/-- The image under a functor of a comparison of two isomorphisms with a common target,
composed with a further isomorphism out of the image of that target. -/
private theorem map_comp_trans_hom {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {X Y Z : C} (e : X ≅ Y) (b : Y ≅ Z) (a : X ≅ Z) (hb : e.hom ≫ b.hom = a.hom)
    {W : D} (c : F.obj Z ≅ W) :
    F.map e.hom ≫ (F.mapIso b ≪≫ c).hom = (F.mapIso a ≪≫ c).hom := by
  simp only [Iso.trans_hom, Functor.mapIso_hom, ← Category.assoc, ← F.map_comp, hb]

/-- The pullback along `φ` of the comparison isomorphism of a cartesian module, composed with the
transition composite along `δ¹₀`, is the transition composite along `δ¹₁`. -/
theorem map_cartesianModuleIso_comp_faceSquare (M : S.CartesianModuleSheaf O)
    {q : SimplexCategory} (φ : ⦋0 + 1⦌ ⟶ q) :
    (S.componentModulePullback O φ).map (S.cartesianModuleIso O M).hom ≫
        (S.faceSquareTransitionModulesIso O M (SimplexCategory.δ (0 : Fin 2)) φ).hom =
      (S.faceSquareTransitionModulesIso O M (SimplexCategory.δ (1 : Fin 2)) φ).hom :=
  map_comp_trans_hom (S.componentModulePullback O φ) (S.cartesianModuleIso O M)
    (S.componentTransitionIso O M (SimplexCategory.δ (0 : Fin 2)))
    (S.componentTransitionIso O M (SimplexCategory.δ (1 : Fin 2)))
    (S.cartesianModuleIso_hom_comp O M) (S.componentTransitionIso O M φ)

/-- The first identification of the cocycle condition, carried to the transition composites. -/
private theorem glueModulesLeft_comp_faceSquare (M : S.CartesianModuleSheaf O) :
    (S.glueModulesOfEq O (SimplexCategory.δ (1 : Fin 2)) (SimplexCategory.δ (1 : Fin 2))
          (SimplexCategory.δ (2 : Fin 3)) (SimplexCategory.δ (1 : Fin 3))
          (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 2) 0)
          SimplexCategory.delta_one_comp_delta_two
          SimplexCategory.delta_one_comp_delta_one (S.componentModule O M.obj ⦋0⦌)).hom ≫
        (S.faceSquareTransitionModulesIso O M (SimplexCategory.δ (1 : Fin 2))
          (SimplexCategory.δ (1 : Fin 3))).hom =
      (S.faceSquareTransitionModulesIso O M (SimplexCategory.δ (1 : Fin 2))
        (SimplexCategory.δ (2 : Fin 3))).hom :=
  S.glueModulesOfEq_comp_componentTransition O M.obj _ _ _ _ _
    SimplexCategory.delta_one_comp_delta_two SimplexCategory.delta_one_comp_delta_one

/-- The middle identification of the cocycle condition, carried to the transition composites. -/
private theorem glueModulesMiddle_comp_faceSquare (M : S.CartesianModuleSheaf O) :
    (S.glueModulesOfEq O (SimplexCategory.δ (0 : Fin 2)) (SimplexCategory.δ (1 : Fin 2))
          (SimplexCategory.δ (2 : Fin 3)) (SimplexCategory.δ (0 : Fin 3))
          (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 2) 1)
          SimplexCategory.delta_zero_comp_delta_two
          SimplexCategory.delta_one_comp_delta_zero (S.componentModule O M.obj ⦋0⦌)).hom ≫
        (S.faceSquareTransitionModulesIso O M (SimplexCategory.δ (1 : Fin 2))
          (SimplexCategory.δ (0 : Fin 3))).hom =
      (S.faceSquareTransitionModulesIso O M (SimplexCategory.δ (0 : Fin 2))
        (SimplexCategory.δ (2 : Fin 3))).hom :=
  S.glueModulesOfEq_comp_componentTransition O M.obj _ _ _ _ _
    SimplexCategory.delta_zero_comp_delta_two SimplexCategory.delta_one_comp_delta_zero

/-- The last identification of the cocycle condition, carried to the transition composites. -/
private theorem glueModulesRight_comp_faceSquare (M : S.CartesianModuleSheaf O) :
    (S.glueModulesOfEq O (SimplexCategory.δ (0 : Fin 2)) (SimplexCategory.δ (0 : Fin 2))
          (SimplexCategory.δ (0 : Fin 3)) (SimplexCategory.δ (1 : Fin 3))
          (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 2) 2)
          SimplexCategory.delta_zero_comp_delta_zero
          SimplexCategory.delta_zero_comp_delta_one (S.componentModule O M.obj ⦋0⦌)).hom ≫
        (S.faceSquareTransitionModulesIso O M (SimplexCategory.δ (0 : Fin 2))
          (SimplexCategory.δ (1 : Fin 3))).hom =
      (S.faceSquareTransitionModulesIso O M (SimplexCategory.δ (0 : Fin 2))
        (SimplexCategory.δ (0 : Fin 3))).hom :=
  S.glueModulesOfEq_comp_componentTransition O M.obj _ _ _ _ _
    SimplexCategory.delta_zero_comp_delta_zero SimplexCategory.delta_zero_comp_delta_one

/-- The three identifications of the cocycle condition, written as the pullback compositors at
the factorizations of the vertices of `⦋2⦌`. -/
private theorem glueModulesLeft_eq (F : (S.componentRingedTopos O ⦋0⦌).Modules) :
    S.glueModulesLeft O F =
      S.glueModulesOfEq O (SimplexCategory.δ (1 : Fin 2)) (SimplexCategory.δ (1 : Fin 2))
        (SimplexCategory.δ (2 : Fin 3)) (SimplexCategory.δ (1 : Fin 3))
        (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 2) 0)
        SimplexCategory.delta_one_comp_delta_two
        SimplexCategory.delta_one_comp_delta_one F := rfl

/-- The middle identification of the cocycle condition, written as the pullback compositors at
the factorizations of the vertices of `⦋2⦌`. -/
private theorem glueModulesMiddle_eq (F : (S.componentRingedTopos O ⦋0⦌).Modules) :
    S.glueModulesMiddle O F =
      S.glueModulesOfEq O (SimplexCategory.δ (0 : Fin 2)) (SimplexCategory.δ (1 : Fin 2))
        (SimplexCategory.δ (2 : Fin 3)) (SimplexCategory.δ (0 : Fin 3))
        (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 2) 1)
        SimplexCategory.delta_zero_comp_delta_two
        SimplexCategory.delta_one_comp_delta_zero F := rfl

/-- The last identification of the cocycle condition, written as the pullback compositors at the
factorizations of the vertices of `⦋2⦌`. -/
private theorem glueModulesRight_eq (F : (S.componentRingedTopos O ⦋0⦌).Modules) :
    S.glueModulesRight O F =
      S.glueModulesOfEq O (SimplexCategory.δ (0 : Fin 2)) (SimplexCategory.δ (0 : Fin 2))
        (SimplexCategory.δ (0 : Fin 3)) (SimplexCategory.δ (1 : Fin 3))
        (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 2) 2)
        SimplexCategory.delta_zero_comp_delta_zero
        SimplexCategory.delta_zero_comp_delta_one F := rfl

/-- The cocycle condition on the comparison isomorphism of a cartesian module, with the three
identifications written as the pullback compositors at the factorizations of the vertices
of `⦋2⦌`. -/
private theorem cartesianModuleIso_cocycle_aux (M : S.CartesianModuleSheaf O) :
    (S.componentModulePullback O (SimplexCategory.δ (1 : Fin 3))).map
        (S.cartesianModuleIso O M).hom =
      (S.glueModulesOfEq O (SimplexCategory.δ (1 : Fin 2)) (SimplexCategory.δ (1 : Fin 2))
            (SimplexCategory.δ (2 : Fin 3)) (SimplexCategory.δ (1 : Fin 3))
            (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 2) 0)
            SimplexCategory.delta_one_comp_delta_two
            SimplexCategory.delta_one_comp_delta_one (S.componentModule O M.obj ⦋0⦌)).inv ≫
        (S.componentModulePullback O (SimplexCategory.δ (2 : Fin 3))).map
            (S.cartesianModuleIso O M).hom ≫
          (S.glueModulesOfEq O (SimplexCategory.δ (0 : Fin 2)) (SimplexCategory.δ (1 : Fin 2))
              (SimplexCategory.δ (2 : Fin 3)) (SimplexCategory.δ (0 : Fin 3))
              (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 2) 1)
              SimplexCategory.delta_zero_comp_delta_two
              SimplexCategory.delta_one_comp_delta_zero (S.componentModule O M.obj ⦋0⦌)).hom ≫
            (S.componentModulePullback O (SimplexCategory.δ (0 : Fin 3))).map
                (S.cartesianModuleIso O M).hom ≫
              (S.glueModulesOfEq O (SimplexCategory.δ (0 : Fin 2))
                (SimplexCategory.δ (0 : Fin 2)) (SimplexCategory.δ (0 : Fin 3))
                (SimplexCategory.δ (1 : Fin 3))
                (SimplexCategory.const (SimplexCategory.mk 0) (SimplexCategory.mk 2) 2)
                SimplexCategory.delta_zero_comp_delta_zero
                SimplexCategory.delta_zero_comp_delta_one
                (S.componentModule O M.obj ⦋0⦌)).hom := by
  refine (Iso.cancel_iso_hom_right _ _ (S.faceSquareTransitionModulesIso O M
    (SimplexCategory.δ (0 : Fin 2)) (SimplexCategory.δ (1 : Fin 3)))).mp ?_
  rw [S.map_cartesianModuleIso_comp_faceSquare O M (SimplexCategory.δ (1 : Fin 3))]
  simp only [Category.assoc]
  rw [S.glueModulesRight_comp_faceSquare O M,
    S.map_cartesianModuleIso_comp_faceSquare O M (SimplexCategory.δ (0 : Fin 3)),
    S.glueModulesMiddle_comp_faceSquare O M,
    S.map_cartesianModuleIso_comp_faceSquare O M (SimplexCategory.δ (2 : Fin 3)),
    ← S.glueModulesLeft_comp_faceSquare O M, Iso.inv_hom_id_assoc]

/-- The comparison isomorphism of a cartesian module satisfies the cocycle
condition in degree two. -/
theorem cartesianModuleIso_cocycle (M : S.CartesianModuleSheaf O) :
    S.IsModuleCocycle O (S.componentModule O M.obj ⦋0⦌) (S.cartesianModuleIso O M) := by
  refine (S.cartesianModuleIso_cocycle_aux O M).trans ?_
  rw [← S.glueModulesLeft_eq O, ← S.glueModulesMiddle_eq O, ← S.glueModulesRight_eq O]

/-- The pair attached to a cartesian module: its degree-zero restriction with
the comparison isomorphism built from the transitions. -/
noncomputable def pairOfCartesianModule (M : S.CartesianModuleSheaf O) :
    CartesianModulePair S O where
  module := S.componentModule O M.obj ⦋0⦌
  iso := S.cartesianModuleIso O M
  cocycle := S.cartesianModuleIso_cocycle O M

/-- The comparison isomorphisms of cartesian modules are natural. -/
theorem cartesianModuleIso_naturality {M N : S.CartesianModuleSheaf O} (f : M ⟶ N) :
    (S.componentModulePullback O (SimplexCategory.δ (1 : Fin 2))).map
          (S.componentModuleMap O f.hom ⦋0⦌) ≫ (S.cartesianModuleIso O N).hom =
      (S.cartesianModuleIso O M).hom ≫
        (S.componentModulePullback O (SimplexCategory.δ (0 : Fin 2))).map
          (S.componentModuleMap O f.hom ⦋0⦌) := by
  refine (Iso.cancel_iso_hom_right _ _
    (S.componentTransitionIso O N (SimplexCategory.δ (0 : Fin 2)))).mp ?_
  rw [Category.assoc, S.cartesianModuleIso_hom_comp O N,
    S.componentTransitionIso_naturality O f (SimplexCategory.δ (1 : Fin 2)),
    Category.assoc, S.componentTransitionIso_naturality O f (SimplexCategory.δ (0 : Fin 2)),
    ← Category.assoc, S.cartesianModuleIso_hom_comp O M]

/-- The functor of Stacks 07TH. The category of cartesian sheaves of `O`-modules on the total
site of a simplicial-site situation maps to the category of pairs `(ℱ, α)` consisting of an
`O₀`-module `ℱ` and an isomorphism `α : f_{δ¹₁}^*ℱ ≅ f_{δ¹₀}^*ℱ` of `O₁`-modules satisfying the
cocycle condition `f_{δ²₁}^*α = f_{δ²₀}^*α ∘ f_{δ²₂}^*α` on `O₂`-modules, by taking the
degree-zero restriction and the comparison of its two transitions to degree one. -/
noncomputable def cartesianModulePairFunctor :
    S.CartesianModuleSheaf O ⥤ CartesianModulePair S O where
  obj := S.pairOfCartesianModule O
  map f := ⟨S.componentModuleMap O f.hom ⦋0⦌, S.cartesianModuleIso_naturality O f⟩
  map_id M := CartesianModulePair.hom_ext S O (S.componentModuleMap_id O M.obj ⦋0⦌)
  map_comp f g := CartesianModulePair.hom_ext S O
    (S.componentModuleMap_comp O f.hom g.hom ⦋0⦌)

/-- The degree-zero module of the pair attached to a cartesian module is its degree-zero
restriction. -/
theorem cartesianModulePairFunctor_obj_module (M : S.CartesianModuleSheaf O) :
    ((S.cartesianModulePairFunctor O).obj M).module = S.componentModule O M.obj ⦋0⦌ := rfl

/-- The comparison isomorphism of the pair attached to a cartesian module is the comparison of
the two transitions to degree one; it is pinned by
`CategoryTheory.SimplicialSiteSituation.cartesianModuleIso_hom_comp`. -/
theorem cartesianModulePairFunctor_obj_iso (M : S.CartesianModuleSheaf O) :
    ((S.cartesianModulePairFunctor O).obj M).iso = S.cartesianModuleIso O M := rfl

/-- The morphism of degree-zero modules underlying the image of a morphism of cartesian modules
is its degree-zero restriction. -/
theorem cartesianModulePairFunctor_map_map {M N : S.CartesianModuleSheaf O} (f : M ⟶ N) :
    ((S.cartesianModulePairFunctor O).map f).map = S.componentModuleMap O f.hom ⦋0⦌ := rfl

/-! ### Faithfulness -/

/-- **Stacks 09WF** for sheaves of modules. A morphism of sheaves of `O`-modules on the total
site is determined by its restrictions to the simplicial components. -/
theorem totalModule_hom_ext {M N : SheafOfModules.{u} (S.totalRingSheaf O)} {α β : M ⟶ N}
    (h : ∀ n : SimplexCategory, S.componentModuleMap O α n = S.componentModuleMap O β n) :
    α = β :=
  hom_ext_moduleSheafFunctor (R := S.totalRingSheaf O) (α := α) (β := β)
    (S.total_hom_ext fun n => congrArg
      (fun t => (Sheaf.moduleSheafFunctor
        (S.componentRingSheaf (S.totalRingSheaf O) n)).map t) (h n))

/-- The functor from cartesian modules to pairs is faithful. -/
instance cartesianModulePairFunctor_faithful :
    (S.cartesianModulePairFunctor O).Faithful where
  map_injective {M N} {f g} hfg := by
    have h0 : S.componentModuleMap O f.hom ⦋0⦌ = S.componentModuleMap O g.hom ⦋0⦌ :=
      congrArg CartesianModulePair.Hom.map hfg
    refine ObjectProperty.hom_ext _ (S.totalModule_hom_ext O fun n => ?_)
    refine (Iso.cancel_iso_hom_left
      (S.componentTransitionIso O M
        (SimplexCategory.const (SimplexCategory.mk 0) n (Fin.last n.len))) _ _).mp ?_
    rw [← S.componentTransitionIso_naturality O f
        (SimplexCategory.const (SimplexCategory.mk 0) n (Fin.last n.len)),
      ← S.componentTransitionIso_naturality O g
        (SimplexCategory.const (SimplexCategory.mk 0) n (Fin.last n.len)), h0]

end CategoryTheory.SimplicialSiteSituation

end
