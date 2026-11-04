module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products

/-!
# The cofree presheaf of modules on an object

Let `R : Cᵒᵖ ⥤ RingCat` be a presheaf of rings, let `W₀ : Cᵒᵖ` and let `J` be an
`R(W₀)`-module. The *cofree* presheaf of `R`-modules on `W₀` with value `J` is

`T ↦ ∏_{g : T ⟶ W₀} J`,

where the factor indexed by `g` carries the `R(T)`-module structure obtained by restriction of
scalars along `R.map g : R(T) ⟶ R(W₀)`. Its restriction maps are reindexings: the factor of
`cofreeOne W₀ J` over `T'` indexed by `g` is read off from the factor over `T` indexed by
`f ≫ g`, which is semilinear in the right direction because
`R.map (f ≫ g) = R.map f ≫ R.map g`.

This presheaf of modules corepresents evaluation at `W₀`: a morphism of presheaves of modules
`Q ⟶ cofreeOne W₀ J` is the same thing as a morphism of `R(W₀)`-modules `Q(W₀) ⟶ J`. It is the
presheaf-of-modules analogue of the cofree presheaf `Stacks.CategoryTheory.CechComplex.cofreeOne`.

## Main definitions

* `Stacks.CategoryTheory.PresheafOfModules.cofreeOne W₀ J` is the cofree presheaf of
  `R`-modules on `W₀` with value `J`, and `cofreeOneπ` are its projections.
* `Stacks.CategoryTheory.PresheafOfModules.cofreeOneDesc` turns a morphism of `R(W₀)`-modules
  `Q(W₀) ⟶ J` into a morphism of presheaves of modules `Q ⟶ cofreeOne W₀ J`, and
  `cofreeOneEval` is the inverse construction.

## Main results

* `Stacks.CategoryTheory.PresheafOfModules.cofreeOneHomEquiv`: `cofreeOne W₀ J` corepresents
  evaluation at `W₀`, that is, `(Q ⟶ cofreeOne W₀ J) ≃ (Q.obj W₀ ⟶ J)`.
* `Stacks.CategoryTheory.PresheafOfModules.cofreeOneMap_comp_cofreeOneπ`: the restriction maps
  of `cofreeOne W₀ J` are reindexings of the factors.
* `Stacks.CategoryTheory.PresheafOfModules.cofreeOneDesc_app_comp_cofreeOneπ` computes the
  components of `cofreeOneDesc`.

## Implementation notes

The index type of the product is the type of morphisms `T ⟶ W₀`, which lives in the morphism
universe `v₁` of `C`; the module universe is `v`, and the hypothesis relating them is
`UnivLE.{v₁, v}`, which is exactly what makes those products exist in `ModuleCat.{v}`. There is
no reindexing and no `ULift`.

The restriction maps are built from `CategoryTheory.Limits.piComparison` for
`ModuleCat.restrictScalars`, which is an isomorphism by
`ModuleCat.preservesLimit_restrictScalars`: a morphism *into* a restriction of scalars of a
product cannot be given by the universal property of that product directly, because restriction
of scalars changes the ambient category.

`cofreeOneMap_comp_cofreeOneπ'` states the reindexing with the composite `f ≫ g` replaced by an
arbitrary `k : T ⟶ W₀` together with an equation `k = f ≫ g`, since the index of a projection
occurs in the type of that projection.

## References

* [Stacks Project, Tag 01EP](https://stacks.math.columbia.edu/tag/01EP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v v₁ u₁ u

attribute [local instance] ModuleCat.hasLimitsOfSize

namespace Stacks.CategoryTheory.PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}} [UnivLE.{v₁, v}]
  (W₀ : Cᵒᵖ) (J : ModuleCat.{v} (R.obj W₀))

/-! ### The underlying family of modules -/

/-- The factor of the cofree presheaf of modules over `T` indexed by a morphism `g : T ⟶ W₀`:
the module `J`, viewed as an `R(T)`-module by restriction of scalars along `R.map g`. -/
noncomputable abbrev cofreeOneFactor (T : Cᵒᵖ) (g : T ⟶ W₀) : ModuleCat.{v} (R.obj T) :=
  (ModuleCat.restrictScalars (R.map g).hom).obj J

/-- The value of the cofree presheaf of modules on `W₀` with value `J` over an object `T`: the
product, indexed by the morphisms `g : T ⟶ W₀`, of copies of `J` restricted along
`R.map g`. -/
noncomputable abbrev cofreeOneObj (T : Cᵒᵖ) : ModuleCat.{v} (R.obj T) :=
  ∏ᶜ fun g : T ⟶ W₀ ↦ cofreeOneFactor W₀ J T g

/-- The projection of `cofreeOneObj W₀ J T` onto the factor indexed by `g : T ⟶ W₀`. -/
noncomputable abbrev cofreeOneπ {T : Cᵒᵖ} (g : T ⟶ W₀) :
    cofreeOneObj W₀ J T ⟶ cofreeOneFactor W₀ J T g :=
  Pi.π _ g

/-- Two morphisms into `cofreeOneObj W₀ J T` agree as soon as they agree after composing with
every projection. -/
@[ext]
theorem cofreeOneObj_hom_ext {T : Cᵒᵖ} {A : ModuleCat.{v} (R.obj T)}
    {x y : A ⟶ cofreeOneObj W₀ J T}
    (h : ∀ g : T ⟶ W₀, x ≫ cofreeOneπ W₀ J g = y ≫ cofreeOneπ W₀ J g) : x = y :=
  Pi.hom_ext _ _ h

/-- The morphism into `cofreeOneObj W₀ J T` determined by a family of morphisms into the
factors. -/
noncomputable abbrev cofreeOneObjLift {T : Cᵒᵖ} {A : ModuleCat.{v} (R.obj T)}
    (x : ∀ g : T ⟶ W₀, A ⟶ cofreeOneFactor W₀ J T g) : A ⟶ cofreeOneObj W₀ J T :=
  Pi.lift x

/-- The projection onto the factor indexed by `g` of the morphism `cofreeOneObjLift W₀ J x` is
`x g`. -/
@[reassoc]
theorem cofreeOneObjLift_comp_cofreeOneπ {T : Cᵒᵖ} {A : ModuleCat.{v} (R.obj T)}
    (x : ∀ g : T ⟶ W₀, A ⟶ cofreeOneFactor W₀ J T g) (g : T ⟶ W₀) :
    cofreeOneObjLift W₀ J x ≫ cofreeOneπ W₀ J g = x g :=
  Pi.lift_π _ _

/-- **Two morphisms into a restriction of scalars of `cofreeOneObj W₀ J T` agree as soon as
they agree after every projection.** Restriction of scalars preserves products, so the
restriction of `cofreeOneObj W₀ J T` is again a product, with the restricted projections. -/
theorem restrictScalars_cofreeOneObj_hom_ext {S : RingCat.{u}} {T : Cᵒᵖ} (a : S ⟶ R.obj T)
    {A : ModuleCat.{v} S}
    {x y : A ⟶ (ModuleCat.restrictScalars a.hom).obj (cofreeOneObj W₀ J T)}
    (h : ∀ g : T ⟶ W₀, x ≫ (ModuleCat.restrictScalars a.hom).map (cofreeOneπ W₀ J g) =
      y ≫ (ModuleCat.restrictScalars a.hom).map (cofreeOneπ W₀ J g)) : x = y :=
  (cancel_mono (piComparison (ModuleCat.restrictScalars a.hom)
      fun g : T ⟶ W₀ ↦ cofreeOneFactor W₀ J T g)).1
    (Pi.hom_ext _ _ fun g ↦ by
      rw [Category.assoc, Category.assoc, piComparison_comp_π]
      exact h g)

/-! ### The restriction maps -/

omit [UnivLE.{v₁, v}] in
/-- The ring map underlying a composite in `Cᵒᵖ` is the composite of the ring maps. This is the
semilinearity of the reindexing maps of the cofree presheaf of modules. -/
theorem map_comp_hom {T T' T'' : Cᵒᵖ} (f : T ⟶ T') (g : T' ⟶ T'') :
    (R.map (f ≫ g)).hom = (R.map g).hom.comp (R.map f).hom :=
  congrArg RingCat.Hom.hom (R.map_comp f g)

/-- The comparison identifying the factor of `cofreeOneObj W₀ J T` at `f ≫ g` with the
restriction along `R.map f` of the factor of `cofreeOneObj W₀ J T'` at `g`. -/
noncomputable def cofreeOneFactorComp {T T' : Cᵒᵖ} (f : T ⟶ T') (g : T' ⟶ W₀) :
    cofreeOneFactor W₀ J T (f ≫ g) ≅
      (ModuleCat.restrictScalars (R.map f).hom).obj (cofreeOneFactor W₀ J T' g) :=
  ModuleCat.restrictScalarsComp'App _ _ _ (map_comp_hom f g) J

/-- The restriction map of the cofree presheaf of modules along `f : T ⟶ T'`: the factor
indexed by `g : T' ⟶ W₀` is read off from the factor indexed by `f ≫ g`. -/
noncomputable def cofreeOneMap {T T' : Cᵒᵖ} (f : T ⟶ T') :
    cofreeOneObj W₀ J T ⟶
      (ModuleCat.restrictScalars (R.map f).hom).obj (cofreeOneObj W₀ J T') :=
  Pi.lift (fun g : T' ⟶ W₀ ↦ cofreeOneπ W₀ J (f ≫ g) ≫ (cofreeOneFactorComp W₀ J f g).hom) ≫
    inv (piComparison (ModuleCat.restrictScalars (R.map f).hom)
      fun g : T' ⟶ W₀ ↦ cofreeOneFactor W₀ J T' g)

/-- **The restriction maps of the cofree presheaf of modules are reindexings.** -/
@[reassoc (attr := simp)]
theorem cofreeOneMap_comp_cofreeOneπ {T T' : Cᵒᵖ} (f : T ⟶ T') (g : T' ⟶ W₀) :
    cofreeOneMap W₀ J f ≫ (ModuleCat.restrictScalars (R.map f).hom).map (cofreeOneπ W₀ J g) =
      cofreeOneπ W₀ J (f ≫ g) ≫ (cofreeOneFactorComp W₀ J f g).hom := by
  rw [cofreeOneMap, Category.assoc, inv_piComparison_comp_map_π]
  exact Pi.lift_π _ _

/-- **The restriction maps of the cofree presheaf of modules are reindexings**, stated for any
`k : T ⟶ W₀` with `k = f ≫ g` in place of the composite `f ≫ g`. -/
@[reassoc]
theorem cofreeOneMap_comp_cofreeOneπ' {T T' : Cᵒᵖ} (f : T ⟶ T') (g : T' ⟶ W₀) (k : T ⟶ W₀)
    (hk : k = f ≫ g) :
    cofreeOneMap W₀ J f ≫ (ModuleCat.restrictScalars (R.map f).hom).map (cofreeOneπ W₀ J g) =
      cofreeOneπ W₀ J k ≫ (ModuleCat.restrictScalarsComp'App (R.map f).hom (R.map g).hom
        (R.map k).hom (by rw [hk]; exact map_comp_hom f g) J).hom := by
  subst hk
  exact cofreeOneMap_comp_cofreeOneπ W₀ J f g

/-- Functoriality of the cofree presheaf of modules: the restriction map along an identity is
the identity. -/
theorem cofreeOneMap_id (T : Cᵒᵖ) :
    cofreeOneMap W₀ J (𝟙 T) = (ModuleCat.restrictScalarsId' (R.map (𝟙 T)).hom
      (congrArg RingCat.Hom.hom (R.map_id T))).inv.app _ := by
  refine restrictScalars_cofreeOneObj_hom_ext W₀ J (R.map (𝟙 T)) fun g ↦ ?_
  rw [cofreeOneMap_comp_cofreeOneπ' W₀ J (𝟙 T) g g (Category.id_comp g).symm]
  refine Eq.trans ?_ (ModuleCat.restrictScalarsId'App_inv_naturality
    (f := (R.map (𝟙 T)).hom) (hf := congrArg RingCat.Hom.hom (R.map_id T))
    (cofreeOneπ W₀ J g))
  refine congrArg (cofreeOneπ W₀ J g ≫ ·) ?_
  ext x
  rfl

/-- Functoriality of the cofree presheaf of modules: the restriction map along a composite is
the composite of the restriction maps. -/
theorem cofreeOneMap_comp {T T' T'' : Cᵒᵖ} (f : T ⟶ T') (g : T' ⟶ T'') :
    cofreeOneMap W₀ J (f ≫ g) = cofreeOneMap W₀ J f ≫
      (ModuleCat.restrictScalars (R.map f).hom).map (cofreeOneMap W₀ J g) ≫
      (ModuleCat.restrictScalarsComp' (R.map f).hom (R.map g).hom (R.map (f ≫ g)).hom
        (map_comp_hom f g)).inv.app _ := by
  refine restrictScalars_cofreeOneObj_hom_ext W₀ J (R.map (f ≫ g)) fun h ↦ ?_
  simp only [Category.assoc]
  rw [cofreeOneMap_comp_cofreeOneπ' W₀ J (f ≫ g) h (f ≫ g ≫ h) (Category.assoc f g h).symm,
    ModuleCat.restrictScalarsComp'_inv_app,
    ← ModuleCat.restrictScalarsComp'App_inv_naturality,
    ← CategoryTheory.Functor.map_comp_assoc, cofreeOneMap_comp_cofreeOneπ W₀ J g h,
    CategoryTheory.Functor.map_comp_assoc,
    cofreeOneMap_comp_cofreeOneπ'_assoc W₀ J f (g ≫ h) (f ≫ g ≫ h) rfl]
  refine congrArg (cofreeOneπ W₀ J (f ≫ g ≫ h) ≫ ·) ?_
  ext x
  rfl

/-- **The cofree presheaf of `R`-modules on `W₀` with value `J`**: it sends `T` to the product
of copies of `J` indexed by the morphisms `T ⟶ W₀`, the factor at `g` being an `R(T)`-module by
restriction of scalars along `R.map g`. It corepresents evaluation at `W₀`, see
`cofreeOneHomEquiv`. -/
@[reducible] noncomputable def cofreeOne : _root_.PresheafOfModules.{v} R where
  obj T := cofreeOneObj W₀ J T
  map f := cofreeOneMap W₀ J f
  map_id T := cofreeOneMap_id W₀ J T
  map_comp f g := cofreeOneMap_comp W₀ J f g

/-- The value of `cofreeOne W₀ J` at `T` is `cofreeOneObj W₀ J T`. -/
@[simp]
theorem cofreeOne_obj (T : Cᵒᵖ) : (cofreeOne W₀ J).obj T = cofreeOneObj W₀ J T :=
  rfl

/-- The restriction map of `cofreeOne W₀ J` along `f` is `cofreeOneMap W₀ J f`. -/
@[simp]
theorem cofreeOne_map {T T' : Cᵒᵖ} (f : T ⟶ T') :
    (cofreeOne W₀ J).map f = cofreeOneMap W₀ J f :=
  rfl

/-! ### Corepresentability of evaluation -/

variable (Q : _root_.PresheafOfModules.{v} R)

/-- **The morphism of presheaves of modules `Q ⟶ cofreeOne W₀ J` determined by a morphism of
`R(W₀)`-modules `Q(W₀) ⟶ J`**: its component at `T` sends a section to the family of the
images of its restrictions along the morphisms `g : T ⟶ W₀`. -/
noncomputable def cofreeOneDesc (α : Q.obj W₀ ⟶ J) : Q ⟶ cofreeOne W₀ J where
  app T := cofreeOneObjLift W₀ J fun g ↦
    Q.map g ≫ (ModuleCat.restrictScalars (R.map g).hom).map α
  naturality {T T'} f := by
    refine restrictScalars_cofreeOneObj_hom_ext W₀ J (R.map f) fun g ↦ ?_
    simp only [Category.assoc]
    rw [← CategoryTheory.Functor.map_comp, cofreeOneObjLift_comp_cofreeOneπ,
      cofreeOneMap_comp_cofreeOneπ, cofreeOneObjLift_comp_cofreeOneπ_assoc, Q.map_comp,
      ModuleCat.restrictScalarsComp'_inv_app]
    simp only [Category.assoc]
    rw [← ModuleCat.restrictScalarsComp'App_inv_naturality_assoc, cofreeOneFactorComp,
      Iso.inv_hom_id, Category.comp_id, CategoryTheory.Functor.map_comp]

/-- The component of `cofreeOneDesc W₀ J Q α` at `T`, followed by the projection onto the
factor indexed by `g : T ⟶ W₀`, is the restriction `Q.map g` followed by `α`. -/
@[reassoc (attr := simp)]
theorem cofreeOneDesc_app_comp_cofreeOneπ (α : Q.obj W₀ ⟶ J) {T : Cᵒᵖ} (g : T ⟶ W₀) :
    (cofreeOneDesc W₀ J Q α).app T ≫ cofreeOneπ W₀ J g =
      Q.map g ≫ (ModuleCat.restrictScalars (R.map g).hom).map α :=
  cofreeOneObjLift_comp_cofreeOneπ W₀ J _ g

/-- The morphism of `R(W₀)`-modules `Q(W₀) ⟶ J` determined by a morphism of presheaves of
modules `Q ⟶ cofreeOne W₀ J`: evaluate at `W₀` and project onto the factor indexed by the
identity. -/
noncomputable def cofreeOneEval (φ : Q ⟶ cofreeOne W₀ J) : Q.obj W₀ ⟶ J :=
  φ.app W₀ ≫ cofreeOneπ W₀ J (𝟙 W₀) ≫
    (ModuleCat.restrictScalarsId'App (R.map (𝟙 W₀)).hom
      (congrArg RingCat.Hom.hom (R.map_id W₀)) J).hom

/-- **`cofreeOne W₀ J` corepresents evaluation at `W₀`.** A morphism of presheaves of modules
`Q ⟶ cofreeOne W₀ J` is the same thing as a morphism of `R(W₀)`-modules `Q(W₀) ⟶ J`. -/
noncomputable def cofreeOneHomEquiv : (Q ⟶ cofreeOne W₀ J) ≃ (Q.obj W₀ ⟶ J) where
  toFun := cofreeOneEval W₀ J Q
  invFun := cofreeOneDesc W₀ J Q
  left_inv φ := by
    refine _root_.PresheafOfModules.hom_ext fun T ↦ cofreeOneObj_hom_ext W₀ J fun g ↦ ?_
    rw [cofreeOneDesc_app_comp_cofreeOneπ, cofreeOneEval, CategoryTheory.Functor.map_comp,
      _root_.PresheafOfModules.Hom.naturality_assoc, CategoryTheory.Functor.map_comp,
      cofreeOneMap_comp_cofreeOneπ'_assoc W₀ J g (𝟙 W₀) g (Category.comp_id g).symm]
    ext x
    rfl
  right_inv α := by
    rw [cofreeOneEval, cofreeOneDesc_app_comp_cofreeOneπ_assoc, Q.map_id,
      ModuleCat.restrictScalarsId'_inv_app,
      ← ModuleCat.restrictScalarsId'App_inv_naturality_assoc, Iso.inv_hom_id, Category.comp_id]

end Stacks.CategoryTheory.PresheafOfModules

end
