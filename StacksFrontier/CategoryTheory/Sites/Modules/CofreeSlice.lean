module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pushforward
public import Mathlib.CategoryTheory.Comma.Over.Basic
public import StacksFrontier.CategoryTheory.Sites.Modules.CofreeForget

/-!
# Restricting a cofree presheaf of modules to a slice category

Let `C` be a thin category, let `R : Cᵒᵖ ⥤ RingCat` be a presheaf of rings and let `V : C`. A
presheaf of `R`-modules may be restricted to the objects of `C` over `V` and then, since
`Over.mk (𝟙 V)` is a terminal object of `Over V`, regarded as a presheaf of modules over the
single ring `R(V)` of sections on `V`; this is the functor `sliceFunctor V` below, the functor
computing the sections used by the module-valued Čech complex of [Stacks, Tag 01EP].

This file identifies the image under `sliceFunctor V` of the cofree presheaf of modules
`Stacks.CategoryTheory.PresheafOfModules.cofreeOne (op W) J` of
`StacksFrontier/CategoryTheory/Sites/Modules/Cofree.lean`. For `W` carrying a morphism
`h : W ⟶ V`, the image is the plain cofree presheaf
`Stacks.CategoryTheory.CechComplex.cofreeOne (Over.mk h) J'` of
`StacksFrontier/CategoryTheory/Sites/CechCofree.lean`, where `J'` is `J` regarded as an
`R(V)`-module; for `W` with no morphism to `V` the image is zero. Together these are what
makes the positive-degree Čech vanishing of `CechCofree.lean` applicable to the module-valued
Čech complex of a covering of `V`.

## Main definitions

* `Stacks.CategoryTheory.PresheafOfModules.sliceFunctor V` restricts a presheaf of `R`-modules
  to the objects over `V`, regarded as a presheaf of `R(V)`-modules.
* `Stacks.CategoryTheory.PresheafOfModules.sliceIndex h T` is the reindexing bijection between
  the morphisms `Over.mk h ⟶ T` of the slice category and the morphisms `W ⟶ T.left` of `C`.
* `Stacks.CategoryTheory.PresheafOfModules.sliceCofreeValue h J` is `J`, regarded as an
  `R(V)`-module.
* `Stacks.CategoryTheory.PresheafOfModules.sliceCofreeOneIso` is the comparison isomorphism.

## Main results

* `Stacks.CategoryTheory.PresheafOfModules.sliceCompEq`: in a thin category the restriction maps
  of `R` to the objects over `V` are compatible with every morphism over `V`.
* `Stacks.CategoryTheory.PresheafOfModules.sliceCofreeOneIso`: **the restriction to the slice
  over `V` of the cofree presheaf of modules on `W` is the plain cofree presheaf on
  `Over.mk h`.**
* `Stacks.CategoryTheory.PresheafOfModules.isZero_sliceFunctor_obj_cofreeOne`: **the restriction
  to the slice over `V` of the cofree presheaf of modules on an object with no morphism to `V`
  is zero.**

## Implementation notes

`sliceFunctor` is built from `PresheafOfModules.pushforward₀ (Over.forget V) R`, the plain
precomposition functor, rather than from `PresheafOfModules.pushforward` for the identity
morphism of the presheaf of rings on the slice. The two are definitionally equal, and the
difference matters: the second spelling carries a `PresheafOfModules.restrictScalars` along an
identity, and the resulting restriction of scalars of a product is not syntactically a product.

Everything below is stated in the spelling in which the ring of sections at an object `T` over
`V` is `R.obj (op T.left)`, never `((Over.forget V).op ⋙ R).obj (op T)`. The two are
definitionally equal, but `CategoryTheory.Functor.comp` is semireducible, so with both spellings
present a goal mentioning a projection of the product is not type-correct at `implicit`
transparency and every `rw` fails. This is why the comparison is made directly between
`sliceFunctor V` and the plain cofree presheaf, with no intermediate cofree presheaf of modules
over the presheaf of rings of the slice, and why the ring map along which `sliceFunctor V`
restricts scalars is carried as a *separate argument* `a` together with the equation `ha`
describing it: the single crossing between the two spellings then happens in the application of
`sliceCofreeOneIso`, at default transparency.

For the same reason `sliceHom_naturality` takes the restriction map of
`(sliceFunctor V).obj (cofreeOne (op W) J)` and the equation describing it as separate
arguments, exactly as `forgetCofreeOneHom_naturality` does in `CofreeForget.lean`.

Thinness of `C` is used twice, and both times it replaces a hypothesis rather than a proof step:
a morphism `W ⟶ T.left` over `V` is automatically a morphism of the slice, which is what makes
`sliceIndex` a bijection whose *both* round trips hold by `rfl`, and every triangle of
restriction maps commutes, which is `sliceCompEq`.

## References

* [Stacks Project, Tag 01EP](https://stacks.math.columbia.edu/tag/01EP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v v₁ u₁ u

attribute [local instance] ModuleCat.hasLimitsOfSize

namespace Stacks.CategoryTheory.PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}

/-! ### The cofree hull of a presheaf of modules -/

/-- **A morphism of presheaves of modules which is a monomorphism at every object is a
monomorphism.** -/
theorem mono_of_mono_app {M N : _root_.PresheafOfModules.{v} R} (φ : M ⟶ N)
    (hφ : ∀ T, Mono (φ.app T)) : Mono φ :=
  ⟨fun g k hgk ↦ _root_.PresheafOfModules.hom_ext fun T ↦
    (hφ T).right_cancellation _ _ (by
      rw [← _root_.PresheafOfModules.comp_app, ← _root_.PresheafOfModules.comp_app, hgk])⟩

section Hull

variable [UnivLE.{v₁, v}] [Small.{v} C] (M : _root_.PresheafOfModules.{v} R)

/-- **The cofree hull of a presheaf of modules**: the product, over all the objects `W` of `C`,
of the cofree presheaves of modules on `W` with value the sections of `M` over `W`. The
canonical morphism into it is a monomorphism, see `mono_toCofreeHull`.

It is reducible, so that a projection of the product is type-correct without unfolding. -/
noncomputable abbrev cofreeHull : _root_.PresheafOfModules.{v} R :=
  ∏ᶜ fun W : C ↦ cofreeOne (op W) (M.obj (op W))

/-- The canonical morphism from a presheaf of modules into its cofree hull: the component at
`W` is the morphism corresponding, under the corepresentability of evaluation at `W`, to the
identity of the sections over `W`. -/
noncomputable def toCofreeHull : M ⟶ cofreeHull M :=
  Pi.lift fun W : C ↦ cofreeOneDesc (op W) (M.obj (op W)) M (𝟙 _)

/-- **The canonical morphism into the cofree hull is a monomorphism.** At an object `W` its
composite with the projection onto the factor indexed by `W` and the identity of `W` is the
restriction map of `M` along an identity, which is an isomorphism. -/
theorem mono_toCofreeHull : Mono (toCofreeHull M) :=
  mono_of_mono_app _ fun T ↦ by
    obtain ⟨W⟩ := T
    have hiso : IsIso (M.map (𝟙 (op W))) := by
      rw [M.map_id]
      infer_instance
    have hfac : (toCofreeHull M).app (op W) ≫
        ((Pi.π (fun W : C ↦ cofreeOne (op W) (M.obj (op W))) W).app (op W) ≫
          cofreeOneπ (op W) (M.obj (op W)) (𝟙 (op W))) =
        M.map (𝟙 (op W)) := by
      rw [← Category.assoc, ← _root_.PresheafOfModules.comp_app, toCofreeHull, Pi.lift_π,
        cofreeOneDesc_app_comp_cofreeOneπ]
      exact (congrArg (M.map (𝟙 (op W)) ≫ ·)
        (CategoryTheory.Functor.map_id (ModuleCat.restrictScalars (R.map (𝟙 (op W))).hom)
          (M.obj (op W)))).trans (Category.comp_id _)
    exact mono_of_mono_fac hfac

end Hull

/-! ### The sections over the objects of a slice category -/

/-- **A presheaf of `R`-modules, restricted to the objects over `V` and regarded as a presheaf
of modules over the ring `R(V)` of sections on `V`.** The restriction of scalars is along the
unique morphism from the terminal object `Over.mk (𝟙 V)` of the slice category. -/
noncomputable def sliceFunctor (V : C) :
    _root_.PresheafOfModules.{v} R ⥤ ((Over V)ᵒᵖ ⥤ ModuleCat.{v} (R.obj (op V))) :=
  _root_.PresheafOfModules.pushforward₀ (Over.forget V) R ⋙
    _root_.PresheafOfModules.forgetToPresheafModuleCat (op (Over.mk (𝟙 V)))
      Over.mkIdTerminal.op

variable [Quiver.IsThin C]

/-- The ring map along which `sliceFunctor V` restricts scalars at an object `T` over `V` is the
restriction of `R` along the structure morphism of `T`. -/
theorem sliceFunctor_ringMap (V : C) (T : (Over V)ᵒᵖ) :
    ((Over.forget V).op ⋙ R).map ((Over.mkIdTerminal (X := V)).op.to T) =
      R.map T.unop.hom.op :=
  congrArg (fun z : T.unop.left ⟶ V ↦ R.map z.op) (Subsingleton.elim _ _)

omit [Quiver.IsThin C] in
/-- `sliceFunctor V` preserves products of any shape small relative to the module universe: at
each object of the slice it is the evaluation of a presheaf of modules followed by a restriction
of scalars, and both of those preserve such products. -/
noncomputable instance sliceFunctor_preservesLimitsOfShape (V : C) (κ : Type v₁)
    [Small.{v} κ] : PreservesLimitsOfShape (Discrete κ) (sliceFunctor.{v} (R := R) V) where
  preservesLimit {G} := preservesLimit_of_evaluation _ _ fun T ↦ by
    have e : sliceFunctor.{v} (R := R) V ⋙ (CategoryTheory.evaluation _ _).obj T ≅
        _root_.PresheafOfModules.evaluation R ((Over.forget V).op.obj T) ⋙
          ModuleCat.restrictScalars (((Over.forget V).op ⋙ R).map
            ((Over.mkIdTerminal (X := V)).op.to T)).hom :=
      NatIso.ofComponents (fun _ ↦ Iso.refl _) fun _ ↦ rfl
    exact preservesLimit_of_natIso _ e.symm

variable {V W : C} (h : W ⟶ V)

/-- **In a thin category every triangle of restriction maps of `R` over `V` commutes.** This is
the semilinearity of all the comparisons below; there is no compatibility hypothesis to carry,
because a morphism between two objects over `V` is automatically a morphism over `V`. -/
theorem sliceCompEq {T T' : Over V} (a : R.obj (op V) ⟶ R.obj (op T.left))
    (ha : a = R.map T.hom.op) (a' : R.obj (op V) ⟶ R.obj (op T'.left))
    (ha' : a' = R.map T'.hom.op) (g : op T.left ⟶ op T'.left) :
    a'.hom = (R.map g).hom.comp a.hom := by
  subst ha
  subst ha'
  rw [← map_comp_hom]
  exact congrArg (fun z : T'.left ⟶ V ↦ (R.map z.op).hom) (Subsingleton.elim _ _)

/-- **The morphisms `Over.mk h ⟶ T` of the slice category over `V` are the morphisms
`W ⟶ T.left` of `C`**, the compatibility with the structure morphisms being automatic in a thin
category. Both round trips hold by `rfl`, which is what keeps the comparisons below free of
dependent rewrites in the index of a product projection. -/
@[simps]
def sliceIndex (T : Over V) : (Over.mk h ⟶ T) ≃ (op T.left ⟶ op W) where
  toFun k := (CommaMorphism.left k).op
  invFun g := Over.homMk g.unop (Subsingleton.elim _ _)
  left_inv _ := rfl
  right_inv _ := rfl

/-! ### The comparison with the plain cofree presheaf -/

variable [UnivLE.{v₁, v}] (J : ModuleCat.{v} (R.obj (op W)))

/-- The value of the cofree presheaf of modules `cofreeOne (op W) J`, regarded as a module over
the ring `R(V)` of sections on `V`. -/
noncomputable abbrev sliceCofreeValue : ModuleCat.{v} (R.obj (op V)) :=
  (ModuleCat.restrictScalars (R.map h.op).hom).obj J

/-- The comparison, for a morphism `g : T.left ⟶ W`, between the value of the plain cofree
presheaf and the factor of `cofreeOne (op W) J` at `g` with its scalars restricted to `R(V)`.
The two agree by `sliceCompEq`. -/
noncomputable def sliceFactor (T : Over V) (a : R.obj (op V) ⟶ R.obj (op T.left))
    (ha : a = R.map T.hom.op) (g : op T.left ⟶ op W) :
    sliceCofreeValue h J ≅
      (ModuleCat.restrictScalars a.hom).obj (cofreeOneFactor (op W) J (op T.left) g) :=
  ModuleCat.restrictScalarsComp'App a.hom (R.map g).hom (R.map h.op).hom
    (sliceCompEq (T' := Over.mk h) a ha (R.map h.op) rfl g) J

/-- The comparison morphism from the sections of the cofree presheaf of modules over `T.left`,
regarded as `R(V)`-modules, to the plain cofree presheaf on `Over.mk h`: the component at a
morphism `k` of the slice is the projection onto the factor indexed by `sliceIndex h T k`, read
through `sliceFactor`. -/
noncomputable def sliceHom (T : Over V) (a : R.obj (op V) ⟶ R.obj (op T.left))
    (ha : a = R.map T.hom.op) :
    (ModuleCat.restrictScalars a.hom).obj (cofreeOneObj (op W) J (op T.left)) ⟶
      (CechComplex.cofreeOne (Over.mk h) (sliceCofreeValue h J)).obj (op T) :=
  CechComplex.cofreeOneLift (Over.mk h) (sliceCofreeValue h J) fun k ↦
    (ModuleCat.restrictScalars a.hom).map (cofreeOneπ (op W) J (sliceIndex h T k)) ≫
      (sliceFactor h J T a ha (sliceIndex h T k)).inv

/-- The comparison morphism from the plain cofree presheaf on `Over.mk h` to the sections of the
cofree presheaf of modules over `T.left`, regarded as `R(V)`-modules. A morphism into a
restriction of scalars of a product is not given by the universal property of that product, so
this is a lift followed by the inverse of `piComparison`. -/
noncomputable def sliceInv (T : Over V) (a : R.obj (op V) ⟶ R.obj (op T.left))
    (ha : a = R.map T.hom.op) :
    (CechComplex.cofreeOne (Over.mk h) (sliceCofreeValue h J)).obj (op T) ⟶
      (ModuleCat.restrictScalars a.hom).obj (cofreeOneObj (op W) J (op T.left)) :=
  Pi.lift (fun g : op T.left ⟶ op W ↦
      CechComplex.cofreeOneπ (Over.mk h) (sliceCofreeValue h J) ((sliceIndex h T).symm g) ≫
        (sliceFactor h J T a ha g).hom) ≫
    inv (piComparison (ModuleCat.restrictScalars a.hom)
      fun g : op T.left ⟶ op W ↦ cofreeOneFactor (op W) J (op T.left) g)

/-- The component of `sliceHom` at a morphism `k` of the slice is the projection of
`cofreeOne (op W) J` onto the factor indexed by `sliceIndex h T k`, followed by the inverse of
`sliceFactor`. -/
@[reassoc]
theorem sliceHom_comp_cofreeOneπ (T : Over V) (a : R.obj (op V) ⟶ R.obj (op T.left))
    (ha : a = R.map T.hom.op) (k : Over.mk h ⟶ T) :
    sliceHom h J T a ha ≫ CechComplex.cofreeOneπ (Over.mk h) (sliceCofreeValue h J) k =
      (ModuleCat.restrictScalars a.hom).map (cofreeOneπ (op W) J (sliceIndex h T k)) ≫
        (sliceFactor h J T a ha (sliceIndex h T k)).inv :=
  CechComplex.cofreeOneLift_comp_cofreeOneπ _ _ _ k

/-- `sliceHom_comp_cofreeOneπ` with the index of the projection of `cofreeOne (op W) J` carried
as a separate argument together with an equation. -/
@[reassoc]
theorem sliceHom_comp_cofreeOneπ' (T : Over V) (a : R.obj (op V) ⟶ R.obj (op T.left))
    (ha : a = R.map T.hom.op) (k : Over.mk h ⟶ T) (g : op T.left ⟶ op W)
    (hg : g = sliceIndex h T k) :
    sliceHom h J T a ha ≫ CechComplex.cofreeOneπ (Over.mk h) (sliceCofreeValue h J) k =
      (ModuleCat.restrictScalars a.hom).map (cofreeOneπ (op W) J g) ≫
        (sliceFactor h J T a ha g).inv := by
  subst hg
  exact sliceHom_comp_cofreeOneπ h J T a ha k

/-- Composing `sliceInv` with the projection of `cofreeOne (op W) J` onto the factor at `g` gives
the projection of the plain cofree presheaf at `(sliceIndex h T).symm g`, followed by
`sliceFactor`. -/
@[reassoc]
theorem sliceInv_comp_map_cofreeOneπ (T : Over V) (a : R.obj (op V) ⟶ R.obj (op T.left))
    (ha : a = R.map T.hom.op) (g : op T.left ⟶ op W) :
    sliceInv h J T a ha ≫ (ModuleCat.restrictScalars a.hom).map (cofreeOneπ (op W) J g) =
      CechComplex.cofreeOneπ (Over.mk h) (sliceCofreeValue h J) ((sliceIndex h T).symm g) ≫
        (sliceFactor h J T a ha g).hom := by
  rw [sliceInv, Category.assoc, inv_piComparison_comp_map_π]
  exact Pi.lift_π _ _

/-- `sliceInv_comp_map_cofreeOneπ` with the index of the projection of the plain cofree presheaf
carried as a separate argument together with an equation. -/
@[reassoc]
theorem sliceInv_comp_map_cofreeOneπ' (T : Over V) (a : R.obj (op V) ⟶ R.obj (op T.left))
    (ha : a = R.map T.hom.op) (g : op T.left ⟶ op W) (k : Over.mk h ⟶ T)
    (hk : k = (sliceIndex h T).symm g) :
    sliceInv h J T a ha ≫ (ModuleCat.restrictScalars a.hom).map (cofreeOneπ (op W) J g) =
      CechComplex.cofreeOneπ (Over.mk h) (sliceCofreeValue h J) k ≫
        (sliceFactor h J T a ha g).hom := by
  subst hk
  exact sliceInv_comp_map_cofreeOneπ h J T a ha g

/-- **The sections of the cofree presheaf of modules `cofreeOne (op W) J` over `T.left`,
regarded as `R(V)`-modules, are the sections of the plain cofree presheaf on `Over.mk h` over
`T`.** -/
@[simps]
noncomputable def sliceIsoApp (T : Over V) (a : R.obj (op V) ⟶ R.obj (op T.left))
    (ha : a = R.map T.hom.op) :
    (ModuleCat.restrictScalars a.hom).obj (cofreeOneObj (op W) J (op T.left)) ≅
      (CechComplex.cofreeOne (Over.mk h) (sliceCofreeValue h J)).obj (op T) where
  hom := sliceHom h J T a ha
  inv := sliceInv h J T a ha
  hom_inv_id := by
    refine restrictScalars_cofreeOneObj_hom_ext (op W) J a fun g ↦ ?_
    rw [Category.assoc, sliceInv_comp_map_cofreeOneπ,
      sliceHom_comp_cofreeOneπ'_assoc h J T a ha ((sliceIndex h T).symm g) g rfl,
      Iso.inv_hom_id, Category.comp_id, Category.id_comp]
  inv_hom_id := by
    refine CechComplex.cofreeOne_obj_hom_ext (Over.mk h) (sliceCofreeValue h J) fun k ↦ ?_
    rw [Category.assoc, sliceHom_comp_cofreeOneπ,
      sliceInv_comp_map_cofreeOneπ'_assoc h J T a ha (sliceIndex h T k) k rfl,
      Iso.hom_inv_id, Category.comp_id, Category.id_comp]

/-- **The comparison morphism is natural.** Both sides project, at a morphism `k` of the slice,
onto the factor indexed by the composite, and the three comparisons of restrictions of scalars
compose to the fourth.

The restriction map `φ` of `(sliceFunctor V).obj (cofreeOne (op W) J)` is taken as a separate
argument together with the equation `hφ` describing it; this is what lets the identification of
the two spellings of the ring of sections on `T.left` happen in an application rather than inside
a goal. -/
theorem sliceHom_naturality {T T' : Over V} (f : T' ⟶ T)
    (a : R.obj (op V) ⟶ R.obj (op T.left)) (ha : a = R.map T.hom.op)
    (a' : R.obj (op V) ⟶ R.obj (op T'.left)) (ha' : a' = R.map T'.hom.op)
    (φ : (ModuleCat.restrictScalars a.hom).obj (cofreeOneObj (op W) J (op T.left)) ⟶
      (ModuleCat.restrictScalars a'.hom).obj (cofreeOneObj (op W) J (op T'.left)))
    (hφ : φ = (ModuleCat.restrictScalars a.hom).map (cofreeOneMap (op W) J f.left.op) ≫
      (ModuleCat.restrictScalarsComp'App a.hom (R.map f.left.op).hom a'.hom
        (sliceCompEq a ha a' ha' f.left.op) (cofreeOneObj (op W) J (op T'.left))).inv) :
    φ ≫ sliceHom h J T' a' ha' =
      sliceHom h J T a ha ≫
        (CechComplex.cofreeOne (Over.mk h) (sliceCofreeValue h J)).map f.op := by
  subst hφ
  refine CechComplex.cofreeOne_obj_hom_ext (Over.mk h) (sliceCofreeValue h J) fun k ↦ ?_
  simp only [Category.assoc]
  rw [sliceHom_comp_cofreeOneπ, CechComplex.cofreeOne_map_comp_cofreeOneπ,
    sliceHom_comp_cofreeOneπ, ← ModuleCat.restrictScalarsComp'App_inv_naturality_assoc,
    ← CategoryTheory.Functor.map_comp_assoc,
    cofreeOneMap_comp_cofreeOneπ' (op W) J f.left.op (sliceIndex h T' k)
      (sliceIndex h T (k ≫ f)) rfl,
    CategoryTheory.Functor.map_comp_assoc]
  refine congrArg ((ModuleCat.restrictScalars a.hom).map
    (cofreeOneπ (op W) J (sliceIndex h T (k ≫ f))) ≫ ·) ?_
  ext x
  rfl

/-- **The restriction to the slice over `V` of the cofree presheaf of modules on `W` is the
plain cofree presheaf on `Over.mk h`** with value `J` regarded as an `R(V)`-module.

This is the comparison which makes
`Stacks.CategoryTheory.CechComplex.isZero_homology_cechComplex_of_retract_of_pi` applicable to
the module-valued Čech complex of a covering of `V`, as in [Stacks, Tag 01EP]. -/
noncomputable def sliceCofreeOneIso :
    (sliceFunctor V).obj (cofreeOne (op W) J) ≅
      CechComplex.cofreeOne (Over.mk h) (sliceCofreeValue h J) :=
  NatIso.ofComponents (fun T ↦ sliceIsoApp h J T.unop _ (sliceFunctor_ringMap V T))
    fun {_ _} f ↦ sliceHom_naturality h J f.unop _ (sliceFunctor_ringMap V _) _
      (sliceFunctor_ringMap V _) _ (by ext x; rfl)

/-! ### Objects with no morphism to the covered one -/

omit [Quiver.IsThin C] in
/-- **The restriction to the slice over `V` of the cofree presheaf of modules on an object
with no morphism to `V` is zero.** The index sets of all its products are empty: a morphism
`W ⟶ T.left` composed with the structure morphism of `T` would be a morphism `W ⟶ V`. -/
theorem isZero_sliceFunctor_obj_cofreeOne (V W : C) (hW : IsEmpty (W ⟶ V))
    (J : ModuleCat.{v} (R.obj (op W))) :
    IsZero ((sliceFunctor.{v} V).obj (cofreeOne (op W) J)) :=
  Functor.isZero _ fun T ↦ (IsZero.iff_id_eq_zero _).2
    (restrictScalars_cofreeOneObj_hom_ext (op W) J
      (((Over.forget V).op ⋙ R).map ((Over.mkIdTerminal (X := V)).op.to T))
      fun g ↦ hW.elim (g.unop ≫ T.unop.hom))

end Stacks.CategoryTheory.PresheafOfModules

end
