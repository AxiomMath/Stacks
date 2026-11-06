module

public import StacksFrontier.CategoryTheory.Sites.CechCofree
public import StacksFrontier.CategoryTheory.Sites.Modules.Cofree

/-!
# The cofree presheaf of modules, viewed as a presheaf of modules over a single ring

Let `R : Cᵒᵖ ⥤ RingCat` be a presheaf of rings and let `X : Cᵒᵖ` be initial, so that
`PresheafOfModules.forgetToPresheafModuleCat X hX` views a presheaf of `R`-modules as a
presheaf of `R(X)`-modules. This file identifies the image under that functor of the cofree
presheaf of modules `Stacks.CategoryTheory.PresheafOfModules.cofreeOne W₀ J` of
`StacksFrontier/CategoryTheory/Sites/Modules/Cofree.lean` with the plain cofree presheaf
`Stacks.CategoryTheory.CechComplex.cofreeOne W₀.unop J'` of
`StacksFrontier/CategoryTheory/Sites/CechCofree.lean`, where `J'` is `J` regarded as an
`R(X)`-module.

This is the comparison needed to apply
`Stacks.CategoryTheory.CechComplex.isZero_homology_cechComplex_of_retract` to a module-valued
Čech complex, as in [Stacks, Tag 01EP]: a splitting of a presheaf of `R`-modules off a cofree
presheaf of modules becomes, under `forgetToPresheafModuleCat`, a splitting off a cofree
presheaf in the sense of the Čech machinery.

## Main definitions

* `Stacks.CategoryTheory.PresheafOfModules.cofreeOneInitialValue X hX W₀ J` is `J`, regarded as
  a module over the ring of sections of `R` at the initial object.
* `Stacks.CategoryTheory.PresheafOfModules.forgetCofreeOneIso` is the comparison isomorphism.

## Main results

* `Stacks.CategoryTheory.PresheafOfModules.forgetToPresheafModuleCat_obj_map_eq`: the
  restriction maps of `(forgetToPresheafModuleCat X hX).obj M` are the restriction maps of `M`,
  read through the comparison of two successive restrictions of scalars.
* `Stacks.CategoryTheory.PresheafOfModules.forgetCofreeOneIso`: the image of `cofreeOne W₀ J`
  under `forgetToPresheafModuleCat X hX` is the plain cofree presheaf on `W₀.unop` with value
  `cofreeOneInitialValue X hX W₀ J`.

## Implementation notes

Both sides are, at an object `T`, a product indexed by the morphisms `T ⟶ W₀`: on the left the
factor at `g` is `J` restricted along `R.map g` and then along `R.map (hX.to T)`, and on the
right it is `J` restricted along `R.map (hX.to W₀)`. The two agree because `hX.to T ≫ g` is
`hX.to W₀` by initiality, so the comparison is `ModuleCat.restrictScalarsComp'App` in each
factor. No reindexing of the product is needed: the index type of
`CechComplex.cofreeOne W₀.unop` at `T` is the type of morphisms `W₀.unop ⟶ T.unop`, and
`Quiver.Hom.op` and `Quiver.Hom.unop` identify it with the type of morphisms `T ⟶ W₀` of `Cᵒᵖ`
by definitional eta for the one-field structure `Opposite`. What *is* needed is
`CategoryTheory.Limits.piComparison` for `ModuleCat.restrictScalars`, an isomorphism by
`ModuleCat.preservesLimit_restrictScalars`, because a morphism into a restriction of scalars of
a product is not given by the universal property of that product.

The hypothesis `UnivLE.{v₁, v}` relating the morphism universe of `C` to the module universe is
the one under which those products exist; it is the same hypothesis as in
`StacksFrontier/CategoryTheory/Sites/Modules/Cofree.lean`.

Everything below is stated in the `ModuleCat.restrictScalars` spelling of the sections of
`cofreeOne W₀ J` and not in the `forgetToPresheafModuleCat` one. The two are definitionally
equal, but `forgetToPresheafModuleCatObj` is semireducible, so with the second spelling in a
stated type the instance `IsIso (piComparison (ModuleCat.restrictScalars _) _)` is not found and
a goal mentioning a projection of the product is not type-correct at `implicit` transparency,
which makes `rw [Category.assoc]` fail. The single crossing between the two spellings happens in
`forgetCofreeOneIso`, where it is a definitional unfolding checked at default transparency.

For the same reason `forgetCofreeOneHom_naturality` takes the restriction map of
`(forgetToPresheafModuleCat X hX).obj (cofreeOne W₀ J)` and the equation describing it as
*separate arguments*: the equation is then used by `exact` at the crossing point rather than by
`rw` inside a goal.

As in `Cofree.lean`, bare `rw [Category.assoc]` is avoided where projection indices are
composites in `Cᵒᵖ`: `rw` abstracts occurrences inside the *proof* arguments of
`cofreeOneMap_comp_cofreeOneπ'`, so it reassociates an index and the motive stops typechecking.

## References

* [Stacks Project, Tag 01EP](https://stacks.math.columbia.edu/tag/01EP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v v₁ u₁ u

attribute [local instance] ModuleCat.hasLimitsOfSize

namespace Stacks.CategoryTheory.PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}} (X : Cᵒᵖ)
  (hX : IsInitial X)

/-! ### The forgetful functor to presheaves of modules over a single ring -/

/-- The ring map from the sections at an initial object factors through the sections at any
intermediate object. This is the semilinearity of the restriction maps of
`PresheafOfModules.forgetToPresheafModuleCat`. -/
theorem mapFromInitial_comp {T T' : Cᵒᵖ} (f : T ⟶ T') :
    (R.map (hX.to T')).hom = (R.map f).hom.comp (R.map (hX.to T)).hom := by
  rw [show hX.to T' = hX.to T ≫ f from hX.hom_ext _ _]
  exact map_comp_hom (R := R) _ _

/-- **The restriction maps of `(forgetToPresheafModuleCat X hX).obj M` are those of `M`**, read
through the comparison between restricting scalars along `R.map (hX.to T')` and restricting
first along `R.map f` and then along `R.map (hX.to T)`. Both sides are the identity on
underlying elements; the content of the statement is that the two `R(X)`-module structures on
the sections of `M` over `T'` agree. -/
theorem forgetToPresheafModuleCat_obj_map_eq (M : _root_.PresheafOfModules.{v} R) {T T' : Cᵒᵖ}
    (f : T ⟶ T') :
    ((_root_.PresheafOfModules.forgetToPresheafModuleCat X hX).obj M).map f =
      (ModuleCat.restrictScalars (R.map (hX.to T)).hom).map (M.map f) ≫
        (ModuleCat.restrictScalarsComp'App (R.map (hX.to T)).hom (R.map f).hom
          (R.map (hX.to T')).hom (mapFromInitial_comp X hX f) (M.obj T')).inv := by
  ext x
  rfl

/-! ### The comparison for the cofree presheaf of modules -/

variable [UnivLE.{v₁, v}] (W₀ : Cᵒᵖ) (J : ModuleCat.{v} (R.obj W₀))

/-- The value of the cofree presheaf of modules `cofreeOne W₀ J`, regarded as a module over the
ring of sections of `R` at the initial object `X`. -/
noncomputable abbrev cofreeOneInitialValue : ModuleCat.{v} (R.obj X) :=
  (ModuleCat.restrictScalars (R.map (hX.to W₀)).hom).obj J

/-- The comparison, for a morphism `g : T ⟶ W₀`, between the value of the plain cofree presheaf
and the factor of `cofreeOne W₀ J` at `g` with its scalars restricted to `R(X)`. The two agree
because `hX.to T ≫ g` is `hX.to W₀`. -/
noncomputable def forgetCofreeOneFactor {T : Cᵒᵖ} (g : T ⟶ W₀) :
    cofreeOneInitialValue X hX W₀ J ≅
      (ModuleCat.restrictScalars (R.map (hX.to T)).hom).obj (cofreeOneFactor W₀ J T g) :=
  ModuleCat.restrictScalarsComp'App _ _ _ (mapFromInitial_comp X hX g) J

/-- The comparison morphism from the sections of the cofree presheaf of modules, regarded as
`R(X)`-modules, to the plain cofree presheaf: the component at a morphism `h` is the projection
onto the factor indexed by `h.op`, read through `forgetCofreeOneFactor`. -/
noncomputable def forgetCofreeOneHom (T : Cᵒᵖ) :
    (ModuleCat.restrictScalars (R.map (hX.to T)).hom).obj (cofreeOneObj W₀ J T) ⟶
      (CechComplex.cofreeOne W₀.unop (cofreeOneInitialValue X hX W₀ J)).obj T :=
  CechComplex.cofreeOneLift W₀.unop (cofreeOneInitialValue X hX W₀ J) fun h ↦
    (ModuleCat.restrictScalars (R.map (hX.to T)).hom).map (cofreeOneπ W₀ J h.op) ≫
      (forgetCofreeOneFactor X hX W₀ J h.op).inv

/-- The projection of `forgetCofreeOneHom` onto the factor of the plain cofree presheaf indexed by
`h` is the projection of `cofreeOne W₀ J` onto the factor indexed by `h.op`, followed by the
inverse of `forgetCofreeOneFactor`. -/
@[reassoc]
theorem forgetCofreeOneHom_comp_cofreeOneπ (T : Cᵒᵖ) (h : W₀.unop ⟶ T.unop) :
    forgetCofreeOneHom X hX W₀ J T ≫
        CechComplex.cofreeOneπ W₀.unop (cofreeOneInitialValue X hX W₀ J) h =
      (ModuleCat.restrictScalars (R.map (hX.to T)).hom).map (cofreeOneπ W₀ J h.op) ≫
        (forgetCofreeOneFactor X hX W₀ J h.op).inv :=
  CechComplex.cofreeOneLift_comp_cofreeOneπ _ _ _ h

/-- `forgetCofreeOneHom_comp_cofreeOneπ` with the index of the projection of `cofreeOne W₀ J`
carried as a separate argument together with an equation, so that no proof below has to rewrite
an index occurring in the type of a projection. -/
@[reassoc]
theorem forgetCofreeOneHom_comp_cofreeOneπ' (T : Cᵒᵖ) (h : W₀.unop ⟶ T.unop) (g : T ⟶ W₀)
    (hg : g = h.op) :
    forgetCofreeOneHom X hX W₀ J T ≫
        CechComplex.cofreeOneπ W₀.unop (cofreeOneInitialValue X hX W₀ J) h =
      (ModuleCat.restrictScalars (R.map (hX.to T)).hom).map (cofreeOneπ W₀ J g) ≫
        (forgetCofreeOneFactor X hX W₀ J g).inv := by
  subst hg
  exact forgetCofreeOneHom_comp_cofreeOneπ X hX W₀ J T h

/-- The comparison morphism from the plain cofree presheaf to the sections of the cofree
presheaf of modules, regarded as `R(X)`-modules. A morphism into a restriction of scalars of a
product is not given by the universal property of that product, so this is a lift followed by
the inverse of `piComparison`. -/
noncomputable def forgetCofreeOneInv (T : Cᵒᵖ) :
    (CechComplex.cofreeOne W₀.unop (cofreeOneInitialValue X hX W₀ J)).obj T ⟶
      (ModuleCat.restrictScalars (R.map (hX.to T)).hom).obj (cofreeOneObj W₀ J T) :=
  Pi.lift (fun g : T ⟶ W₀ ↦
      CechComplex.cofreeOneπ W₀.unop (cofreeOneInitialValue X hX W₀ J) g.unop ≫
        (forgetCofreeOneFactor X hX W₀ J g).hom) ≫
    inv (piComparison (ModuleCat.restrictScalars (R.map (hX.to T)).hom)
      fun g : T ⟶ W₀ ↦ cofreeOneFactor W₀ J T g)

/-- Composing `forgetCofreeOneInv` with the projection of `cofreeOne W₀ J` onto the factor
indexed by `g` gives the projection of the plain cofree presheaf onto the factor indexed by
`g.unop`, followed by `forgetCofreeOneFactor`. -/
@[reassoc]
theorem forgetCofreeOneInv_comp_map_cofreeOneπ (T : Cᵒᵖ) (g : T ⟶ W₀) :
    forgetCofreeOneInv X hX W₀ J T ≫
        (ModuleCat.restrictScalars (R.map (hX.to T)).hom).map (cofreeOneπ W₀ J g) =
      CechComplex.cofreeOneπ W₀.unop (cofreeOneInitialValue X hX W₀ J) g.unop ≫
        (forgetCofreeOneFactor X hX W₀ J g).hom := by
  rw [forgetCofreeOneInv, Category.assoc, inv_piComparison_comp_map_π]
  exact Pi.lift_comp_π _ _

/-- `forgetCofreeOneInv_comp_map_cofreeOneπ` with the index of the projection of the plain
cofree presheaf carried as a separate argument together with an equation. -/
@[reassoc]
theorem forgetCofreeOneInv_comp_map_cofreeOneπ' (T : Cᵒᵖ) (g : T ⟶ W₀)
    (h : W₀.unop ⟶ T.unop) (hh : h = g.unop) :
    forgetCofreeOneInv X hX W₀ J T ≫
        (ModuleCat.restrictScalars (R.map (hX.to T)).hom).map (cofreeOneπ W₀ J g) =
      CechComplex.cofreeOneπ W₀.unop (cofreeOneInitialValue X hX W₀ J) h ≫
        (forgetCofreeOneFactor X hX W₀ J g).hom := by
  subst hh
  exact forgetCofreeOneInv_comp_map_cofreeOneπ X hX W₀ J T g

/-- **The sections of the cofree presheaf of modules `cofreeOne W₀ J` over `T`, regarded as
`R(X)`-modules, are the sections of the plain cofree presheaf on `W₀.unop`.** -/
@[simps]
noncomputable def forgetCofreeOneIsoApp (T : Cᵒᵖ) :
    (ModuleCat.restrictScalars (R.map (hX.to T)).hom).obj (cofreeOneObj W₀ J T) ≅
      (CechComplex.cofreeOne W₀.unop (cofreeOneInitialValue X hX W₀ J)).obj T where
  hom := forgetCofreeOneHom X hX W₀ J T
  inv := forgetCofreeOneInv X hX W₀ J T
  hom_inv_id := by
    refine restrictScalars_cofreeOneObj_hom_ext W₀ J (R.map (hX.to T)) fun g ↦ ?_
    rw [Category.assoc, forgetCofreeOneInv_comp_map_cofreeOneπ,
      forgetCofreeOneHom_comp_cofreeOneπ'_assoc X hX W₀ J T g.unop g rfl, Iso.inv_hom_id,
      Category.comp_id, Category.id_comp]
  inv_hom_id := by
    refine CechComplex.cofreeOne_obj_hom_ext W₀.unop (cofreeOneInitialValue X hX W₀ J) fun h ↦ ?_
    rw [Category.assoc, forgetCofreeOneHom_comp_cofreeOneπ,
      forgetCofreeOneInv_comp_map_cofreeOneπ'_assoc X hX W₀ J T h.op h rfl, Iso.hom_inv_id,
      Category.comp_id, Category.id_comp]

/-- **The comparison morphism is natural.** Both sides project, at a morphism `h`, onto the
factor indexed by the composite, and the three comparisons of restrictions of scalars compose to
the fourth.

The restriction map `φ` of `(forgetToPresheafModuleCat X hX).obj (cofreeOne W₀ J)` is taken as a
separate argument together with the equation `hφ` describing it, which is
`forgetToPresheafModuleCat_obj_map_eq`; this is what lets the identification of the two
spellings of the sections happen in an application rather than inside a goal. -/
theorem forgetCofreeOneHom_naturality {T T' : Cᵒᵖ} (f : T ⟶ T')
    (φ : (ModuleCat.restrictScalars (R.map (hX.to T)).hom).obj (cofreeOneObj W₀ J T) ⟶
      (ModuleCat.restrictScalars (R.map (hX.to T')).hom).obj (cofreeOneObj W₀ J T'))
    (hφ : φ = (ModuleCat.restrictScalars (R.map (hX.to T)).hom).map (cofreeOneMap W₀ J f) ≫
      (ModuleCat.restrictScalarsComp'App (R.map (hX.to T)).hom (R.map f).hom
        (R.map (hX.to T')).hom (mapFromInitial_comp X hX f) (cofreeOneObj W₀ J T')).inv) :
    φ ≫ forgetCofreeOneHom X hX W₀ J T' =
      forgetCofreeOneHom X hX W₀ J T ≫
        (CechComplex.cofreeOne W₀.unop (cofreeOneInitialValue X hX W₀ J)).map f := by
  subst hφ
  refine CechComplex.cofreeOne_obj_hom_ext W₀.unop (cofreeOneInitialValue X hX W₀ J) fun h ↦ ?_
  simp only [Category.assoc]
  rw [forgetCofreeOneHom_comp_cofreeOneπ, CechComplex.cofreeOne_map_comp_cofreeOneπ,
    forgetCofreeOneHom_comp_cofreeOneπ, forgetCofreeOneFactor, forgetCofreeOneFactor,
    ← ModuleCat.restrictScalarsComp'App_inv_naturality_assoc,
    ← CategoryTheory.Functor.map_comp_assoc,
    cofreeOneMap_comp_cofreeOneπ' W₀ J f h.op ((h ≫ f.unop).op)
      (by rw [op_comp, Quiver.Hom.op_unop]),
    CategoryTheory.Functor.map_comp_assoc]
  refine congrArg ((ModuleCat.restrictScalars (R.map (hX.to T)).hom).map
    (cofreeOneπ W₀ J ((h ≫ f.unop).op)) ≫ ·) ?_
  ext x
  rfl

/-- **The image of the cofree presheaf of modules `cofreeOne W₀ J` under
`forgetToPresheafModuleCat X hX` is the plain cofree presheaf on `W₀.unop`** with value `J`
regarded as a module over the ring of sections of `R` at the initial object `X`.

This is the comparison which turns a splitting of a presheaf of `R`-modules off a cofree
presheaf of modules into a splitting off a cofree presheaf in the sense of
`Stacks.CategoryTheory.CechComplex.cofree`, and hence makes
`Stacks.CategoryTheory.CechComplex.isZero_homology_cechComplex_of_retract` applicable to a
module-valued Čech complex. -/
noncomputable def forgetCofreeOneIso :
    (_root_.PresheafOfModules.forgetToPresheafModuleCat X hX).obj (cofreeOne W₀ J) ≅
      CechComplex.cofreeOne W₀.unop (cofreeOneInitialValue X hX W₀ J) :=
  NatIso.ofComponents (forgetCofreeOneIsoApp X hX W₀ J) fun {_ _} f ↦
    forgetCofreeOneHom_naturality X hX W₀ J f _
      (forgetToPresheafModuleCat_obj_map_eq X hX (cofreeOne W₀ J) f)

end Stacks.CategoryTheory.PresheafOfModules

end
