module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.ModuleBarResolution
public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationResolutionTerms

/-!
# The simplex-coefficient resolution of a sheaf of modules, restricted to a component

Let `S` be a simplicial-site situation, `O` a sheaf of rings on its total site and `M` a sheaf of
`O`-modules. Over an object of the component of simplicial degree `m`, the degree-`n` term
`B_n(M)` of the simplex-coefficient resolution of
`StacksFrontier/AlgebraicGeometry/Simplicial/ComponentRingedTopos/ModuleBarResolution.lean` is the
direct sum of copies of `M` indexed by the simplex maps `φ : [n] ⟶ [m]`. So the restriction of
`B_n(M)` to that component is the direct sum `⨁_{φ : [n] ⟶ [m]} M|_m` of copies of the
restriction of `M`, the `φ`th summand inclusion placing a section at the label `φ`.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.barLabel`: over an object of degree `m`, the label of
  the summand of `B_n(M)` attached to a simplex map `φ : [n] ⟶ [m]`.
* `CategoryTheory.SimplicialSiteSituation.moduleBarSummand`: the `φ`th summand inclusion
  `M|_m ⟶ B_n(M)|_m`.
* `CategoryTheory.SimplicialSiteSituation.moduleBarProjection`: the `φ`th summand projection
  `B_n(M)|_m ⟶ M|_m`.
* `CategoryTheory.SimplicialSiteSituation.moduleBarComponentCofan`: the cofan of the summand
  inclusions.

## Main results

* `CategoryTheory.SimplicialSiteSituation.isColimitModuleBarComponentCofan`: **the restriction
  of `B_n(M)` to the component of degree `m` is the direct sum, over the simplex maps
  `φ : [n] ⟶ [m]`, of copies of `M|_m`, with the summand inclusions as legs.**

## Implementation notes

Over the component of degree `m` the labels of `B_n(M)` are the simplex maps from `[n]` into the
simplicial degree of the object, which is `m` only propositionally for a general situation
(`CategoryTheory.SimplicialSiteSituation.totalSimplexDegree_leftOp_obj_op_componentFunctor_obj`);
`barLabel` transports a simplex map `[n] ⟶ [m]` along that equation once, and every statement
about labels is reduced to it.

The morphisms are built with `PresheafOfModules.homMk` from morphisms of the underlying
presheaves of abelian groups, and every equation between them is checked on those presheaves,
which is where restriction of scalars along the identity of the component structure sheaf is
invisible.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pseudofunctor
open scoped Simplicial

universe u

namespace CategoryTheory.SimplicialSiteSituation

attribute [local implicit_reducible] SimplicialSite.totalPseudofunctor
  Functor.toPseudofunctor' pseudofunctorOfIsLocallyDiscrete totalCategory Quiver.Hom.toLoc
  CoGrothendieck.category CoGrothendieck.categoryStruct CoGrothendieck.ι Cat.str
  Grothendieck.ι Grothendieck.instCategory uliftFunctor componentFunctor component
  simplexIndices totalSimplexDegree PresheafOfModules.presheaf

variable {S : SimplicialSiteSituation.{u}} {O : Sheaf S.totalTopology RingCat.{u}}

/-! ### Labels over a component -/

/-- Over an object `U` of the component of degree `m`, the label of the summand of `B_n(M)`
attached to the simplex map `φ : [n] ⟶ [m]`. -/
def barLabel {n m : SimplexCategory} (φ : n ⟶ m) (U : S.component m) :
    (simplexIndices.{u, u} S n).obj (Opposite.op ((componentFunctor S m).obj U)) :=
  ULift.up (φ ≫ eqToHom (S.totalSimplexDegree_leftOp_obj_op_componentFunctor_obj m U).symm)

/-- Distinct simplex maps give distinct labels. -/
theorem barLabel_injective {n m : SimplexCategory} (U : S.component m) :
    Function.Injective fun φ : n ⟶ m => barLabel φ U :=
  fun _ _ h => (cancel_mono (eqToHom _)).1 (congrArg ULift.down h)

/-- Every label over an object of the component of degree `m` is the label of a simplex map
`[n] ⟶ [m]`. -/
theorem barLabel_surjective {n m : SimplexCategory} (U : S.component m)
    (a : (simplexIndices.{u, u} S n).obj (Opposite.op ((componentFunctor S m).obj U))) :
    ∃ φ : n ⟶ m, barLabel φ U = a :=
  ⟨a.down ≫ eqToHom (S.totalSimplexDegree_leftOp_obj_op_componentFunctor_obj m U),
    ULift.ext (by simp [barLabel])⟩

/-- Restriction along a morphism of the component of degree `m` keeps the labels. -/
theorem simplexIndices_map_barLabel {n m : SimplexCategory} (φ : n ⟶ m)
    {U V : S.component m} (g : U ⟶ V) :
    (simplexIndices.{u, u} S n).map ((componentFunctor S m).map g).op (barLabel φ V) =
      barLabel φ U := by
  obtain ⟨c⟩ := S
  cases c <;>
  · apply ULift.ext
    change (φ ≫ 𝟙 m) ≫ _ = φ ≫ 𝟙 m
    simp only [Category.comp_id]
    exact Category.comp_id φ

/-! ### The summand inclusions and projections -/

variable (M : SheafOfModules.{u} O)

/-- Restriction in `B_n(M)` along a morphism of the component of degree `m` carries a section
placed at the label of `φ` to the restricted section placed at the label of `φ`. -/
theorem moduleBarPresheaf_map_single {n m : SimplexCategory} (φ : n ⟶ m) {U V : S.component m}
    (g : U ⟶ V) (x : M.val.obj (Opposite.op ((componentFunctor S m).obj V))) :
    (moduleBarPresheaf M n).map ((componentFunctor S m).map g).op
        (Finsupp.single (barLabel φ V) x) =
      Finsupp.single (barLabel φ U) (M.val.map ((componentFunctor S m).map g).op x) := by
  rw [PresheafOfModules.copowerObj_map_apply, Finsupp.mapRange_single,
    Finsupp.mapDomain_single, simplexIndices_map_barLabel]

/-- Restriction in `B_n(M)` along a morphism of the component of degree `m` keeps the
coefficient at the label of `φ`, restricted. -/
theorem moduleBarPresheaf_map_apply_barLabel {n m : SimplexCategory} (φ : n ⟶ m)
    {U V : S.component m} (g : U ⟶ V)
    (y : (simplexIndices.{u, u} S n).obj (Opposite.op ((componentFunctor S m).obj V)) →₀
      M.val.obj (Opposite.op ((componentFunctor S m).obj V))) :
    (show (simplexIndices.{u, u} S n).obj (Opposite.op ((componentFunctor S m).obj U)) →₀
        M.val.obj (Opposite.op ((componentFunctor S m).obj U)) from
      (moduleBarPresheaf M n).map ((componentFunctor S m).map g).op y) (barLabel φ U) =
      M.val.map ((componentFunctor S m).map g).op (y (barLabel φ V)) := by
  have hinj : Function.Injective (ConcreteCategory.hom ((simplexIndices.{u, u} S n).map
      ((componentFunctor S m).map g).op)) := by
    intro a b h
    obtain ⟨ψ, rfl⟩ := barLabel_surjective V a
    obtain ⟨χ, rfl⟩ := barLabel_surjective V b
    rw [simplexIndices_map_barLabel, simplexIndices_map_barLabel] at h
    rw [barLabel_injective U h]
  refine (congrArg (fun z : (simplexIndices.{u, u} S n).obj
      (Opposite.op ((componentFunctor S m).obj U)) →₀
        M.val.obj (Opposite.op ((componentFunctor S m).obj U)) => z (barLabel φ U))
    (PresheafOfModules.copowerObj_map_apply M.val (simplexIndices.{u, u} S n)
      ((componentFunctor S m).map g).op y)).trans ?_
  conv_lhs => rw [← simplexIndices_map_barLabel φ g]
  exact (Finsupp.mapDomain_apply_of_injective hinj _ _).trans rfl

/-- The `φ`th summand inclusion `M|_m ⟶ B_n(M)|_m`, placing a section at the label of `φ`. -/
def moduleBarSummand {n m : SimplexCategory} (φ : n ⟶ m) :
    (componentModuleRestriction S O m).obj M ⟶
      (componentModuleRestriction S O m).obj (moduleBarSheaf M n) :=
  ⟨PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom (Finsupp.singleAddHom (barLabel φ U.unop))
      naturality := by
        intro U V g
        ext x
        exact (moduleBarPresheaf_map_single M φ g.unop x).symm }
    (fun U r x => (Finsupp.smul_single (r : O.obj.obj (Opposite.op ((componentFunctor S m).obj
      U.unop))) (barLabel φ U.unop) (x : M.val.obj (Opposite.op ((componentFunctor S m).obj
        U.unop)))).symm)⟩

/-- The `φ`th summand projection `B_n(M)|_m ⟶ M|_m`, reading off the coefficient at the label of
`φ`. -/
def moduleBarProjection {n m : SimplexCategory} (φ : n ⟶ m) :
    (componentModuleRestriction S O m).obj (moduleBarSheaf M n) ⟶
      (componentModuleRestriction S O m).obj M :=
  ⟨PresheafOfModules.homMk
    { app := fun U => AddCommGrpCat.ofHom (Finsupp.applyAddHom (barLabel φ U.unop))
      naturality := by
        intro U V g
        ext x
        exact moduleBarPresheaf_map_apply_barLabel M φ g.unop x }
    (fun U r x => rfl)⟩

/-! ### The direct sum decomposition -/

section Decomposition

/-- The simplex maps between two objects of the simplex category form a finite type. -/
noncomputable local instance moduleBarComponentFintypeHom (n m : SimplexCategory) :
    Fintype (n ⟶ m) :=
  Fintype.ofFinite _

variable {m : SimplexCategory}

/-- Morphisms of sheaves of modules on a component agree as soon as they agree on every
section. -/
theorem componentModule_hom_ext {A B : SheafOfModules.{u} (componentRingSheaf S O m)}
    {f g : A ⟶ B} (h : ∀ U (x : A.val.obj U), f.val.app U x = g.val.app U x) : f = g :=
  (SheafOfModules.forget _).map_injective <| PresheafOfModules.hom_ext fun U =>
    ModuleCat.hom_ext <| LinearMap.ext (h U)

/-- A finite sum of morphisms of sheaves of modules is computed section by section. -/
theorem componentModule_sum_val_app {A B : SheafOfModules.{u} (componentRingSheaf S O m)}
    {ι : Type*} (s : Finset ι) (f : ι → (A ⟶ B)) (U) (x : A.val.obj U) :
    (∑ i ∈ s, f i).val.app U x = ∑ i ∈ s, (f i).val.app U x := by
  classical
  induction s using Finset.induction_on with
  | empty => rfl
  | insert i s hi ih =>
    rw [Finset.sum_insert hi, Finset.sum_insert hi, ← ih]
    rfl

variable {n : SimplexCategory}

/-- The `φ`th summand projection of the `φ`th summand inclusion is the identity. -/
@[reassoc (attr := simp)]
theorem moduleBarSummand_comp_moduleBarProjection (φ : n ⟶ m) :
    moduleBarSummand M φ ≫ moduleBarProjection M φ = 𝟙 _ :=
  componentModule_hom_ext fun U x =>
    Finsupp.single_eq_same (a := barLabel φ U.unop)
      (b := (x : M.val.obj (Opposite.op ((componentFunctor S m).obj U.unop))))

/-- A coefficient placed at the label of `ψ` vanishes at the label of `φ` for `ψ ≠ φ`. -/
private theorem single_barLabel_apply_barLabel_of_ne {N : Type*} [Zero N] {φ ψ : n ⟶ m}
    (h : ψ ≠ φ) (U : S.component m) (b : N) :
    Finsupp.single (barLabel ψ U) b (barLabel φ U) = 0 :=
  Finsupp.single_eq_of_ne fun h' => h (barLabel_injective U h'.symm)

/-- The `φ`th summand projection of the `ψ`th summand inclusion vanishes for `ψ ≠ φ`. -/
theorem moduleBarSummand_comp_moduleBarProjection_of_ne {φ ψ : n ⟶ m} (h : ψ ≠ φ) :
    moduleBarSummand M ψ ≫ moduleBarProjection M φ = 0 :=
  componentModule_hom_ext fun U _ => single_barLabel_apply_barLabel_of_ne h U.unop _

/-- The summand projections followed by the summand inclusions add up to the identity. -/
theorem sum_moduleBarProjection_comp_moduleBarSummand :
    ∑ φ : n ⟶ m, moduleBarProjection M φ ≫ moduleBarSummand M φ = 𝟙 _ := by
  refine componentModule_hom_ext fun U x => ?_
  rw [componentModule_sum_val_app]
  let y : (simplexIndices.{u, u} S n).obj (Opposite.op ((componentFunctor S m).obj U.unop)) →₀
      M.val.obj (Opposite.op ((componentFunctor S m).obj U.unop)) := x
  change ∑ φ : n ⟶ m, Finsupp.single (barLabel φ U.unop) (y (barLabel φ U.unop)) = y
  ext a
  obtain ⟨ψ, rfl⟩ := barLabel_surjective U.unop a
  rw [Finsupp.finsetSum_apply, Fintype.sum_eq_single ψ]
  · exact Finsupp.single_eq_same
  · exact fun φ hφ => single_barLabel_apply_barLabel_of_ne hφ U.unop _

/-- The cofan of the summand inclusions of `B_n(M)|_m`. -/
def moduleBarComponentCofan (n m : SimplexCategory) :
    Cofan fun _ : n ⟶ m => (componentModuleRestriction S O m).obj M :=
  Cofan.mk ((componentModuleRestriction S O m).obj (moduleBarSheaf M n))
    (fun φ => moduleBarSummand M φ)

/-- **Over the component of degree `m`, `B_n(M)` is the direct sum of copies of `M|_m` indexed
by the simplex maps `[n] ⟶ [m]`**, the legs being the summand inclusions. -/
def isColimitModuleBarComponentCofan (n m : SimplexCategory) :
    IsColimit (moduleBarComponentCofan M n m) :=
  Cofan.IsColimit.mk _ (fun t => ∑ φ : n ⟶ m, moduleBarProjection M φ ≫ t.inj φ)
    (fun t ψ => by
      change moduleBarSummand M ψ ≫ (∑ φ : n ⟶ m, moduleBarProjection M φ ≫ t.inj φ :
        (componentModuleRestriction S O m).obj (moduleBarSheaf M n) ⟶ t.pt) = t.inj ψ
      rw [Preadditive.comp_sum, Finset.sum_eq_single ψ]
      · rw [moduleBarSummand_comp_moduleBarProjection_assoc]
      · intro φ _ hφ
        rw [← Category.assoc, moduleBarSummand_comp_moduleBarProjection_of_ne M (Ne.symm hφ),
          zero_comp]
      · intro h
        exact absurd (Finset.mem_univ ψ) h)
    (fun t g hg => by
      have key : ∀ g' : (componentModuleRestriction S O m).obj (moduleBarSheaf M n) ⟶ t.pt,
          (∀ φ, moduleBarSummand M φ ≫ g' = t.inj φ) →
            g' = ∑ φ : n ⟶ m, moduleBarProjection M φ ≫ t.inj φ := by
        intro g' hg'
        rw [← Category.id_comp g', ← sum_moduleBarProjection_comp_moduleBarSummand M,
          Preadditive.sum_comp]
        refine Finset.sum_congr rfl fun φ _ => ?_
        rw [Category.assoc, hg' φ]
      exact key g hg)

end Decomposition

end CategoryTheory.SimplicialSiteSituation

end
