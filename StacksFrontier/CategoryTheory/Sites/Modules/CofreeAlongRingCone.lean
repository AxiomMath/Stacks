module

public import StacksFrontier.CategoryTheory.Sites.CechCofree
public import StacksFrontier.CategoryTheory.Sites.Modules.Cofree

/-!
# Presheaves of modules viewed over a ring mapping to all the rings of sections

Let `R : Cᵒᵖ ⥤ RingCat` be a presheaf of rings and let `A` be a ring together with compatible
ring maps `ψ T : A →+* R(T)`, one for each object (a cone over `R` with vertex `A`; the global
sections of a sheaf of rings provide one, and so does any ring mapping to them). Then every
presheaf of `R`-modules is, by restriction of scalars along the `ψ T`, a presheaf of
`A`-modules: this is `toBasePresheaf ψ hψ`. It generalises Mathlib's
`PresheafOfModules.forgetToPresheafModuleCat`, which is the case of the cone `R(X) → R(T)` from
an initial object `X`.

This file records the two properties of `toBasePresheaf` which make the positive-degree Čech
vanishing for cofree presheaves (`StacksFrontier/CategoryTheory/Sites/CechCofree.lean`) applicable
to module-valued Čech complexes: it preserves limits, and it sends the cofree presheaf of modules
`Stacks.CategoryTheory.PresheafOfModules.cofreeOne W₀ J` to the plain cofree presheaf on
`W₀.unop` with value `J` regarded as an `A`-module (`toBasePresheafCofreeOneIso`). The second is
`StacksFrontier/CategoryTheory/Sites/Modules/CofreeForget.lean` with the initial object replaced by
the cone.

## Main definitions

* `Stacks.CategoryTheory.PresheafOfModules.toBasePresheaf ψ hψ` — a presheaf of `R`-modules as a
  presheaf of `A`-modules.
* `Stacks.CategoryTheory.PresheafOfModules.toBasePresheafCofreeOneIso` — the comparison for the
  cofree presheaf of modules.

## Main results

* `Stacks.CategoryTheory.PresheafOfModules.preservesLimit_toBasePresheaf` — `toBasePresheaf`
  preserves every limit.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v v₁ u₁ u uA

attribute [local instance] ModuleCat.hasLimitsOfSize

namespace Stacks.CategoryTheory.PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}} {A : Type uA} [Ring A]

/-- A family of ring maps `ψ T : A →+* R(T)` is a *ring cone* over `R` when it is compatible
with the restriction maps of `R`. -/
abbrev IsRingCone (ψ : ∀ T : Cᵒᵖ, A →+* R.obj T) : Prop :=
  ∀ ⦃T T' : Cᵒᵖ⦄ (f : T ⟶ T'), ψ T' = (R.map f).hom.comp (ψ T)

variable (ψ : ∀ T : Cᵒᵖ, A →+* R.obj T) (hψ : IsRingCone ψ)

/-! ### The functor -/

/-- The sections of a presheaf of `R`-modules over `T`, as an `A`-module. -/
abbrev toBasePresheafObjObj (M : _root_.PresheafOfModules.{v} R) (T : Cᵒᵖ) : ModuleCat.{v} A :=
  (ModuleCat.restrictScalars (ψ T)).obj (M.obj T)

/-- The restriction maps of a presheaf of `R`-modules are `A`-linear. -/
def toBasePresheafObjMap (M : _root_.PresheafOfModules.{v} R) {T T' : Cᵒᵖ} (f : T ⟶ T') :
    toBasePresheafObjObj ψ M T ⟶ toBasePresheafObjObj ψ M T' :=
  ModuleCat.ofHom
    (X := toBasePresheafObjObj ψ M T) (Y := toBasePresheafObjObj ψ M T')
    { toFun := fun x ↦ M.map f x
      map_add' := fun x y ↦ (M.map f).hom.map_add x y
      map_smul' := fun a x ↦ by
        change M.map f (ψ T a • x) = ψ T' a • M.map f x
        rw [hψ f]
        exact M.map_smul f (ψ T a) x }

/-- The restriction maps of `toBasePresheafObj`, on elements. -/
@[simp]
lemma toBasePresheafObjMap_apply (M : _root_.PresheafOfModules.{v} R) {T T' : Cᵒᵖ}
    (f : T ⟶ T') (x : M.obj T) : (toBasePresheafObjMap ψ hψ M f).hom x = M.map f x := rfl

/-- A presheaf of `R`-modules, as a presheaf of `A`-modules. -/
def toBasePresheafObj (M : _root_.PresheafOfModules.{v} R) : Cᵒᵖ ⥤ ModuleCat.{v} A where
  obj T := toBasePresheafObjObj ψ M T
  map f := toBasePresheafObjMap ψ hψ M f
  map_id T := by ext x; exact congrArg (fun g ↦ g.hom x) (M.map_id T)
  map_comp f g := by ext x; exact congrArg (fun h ↦ h.hom x) (M.map_comp f g)

/-- **Presheaves of `R`-modules as presheaves of `A`-modules**, by restriction of scalars along
the ring maps `ψ T : A →+* R(T)`. -/
def toBasePresheaf : _root_.PresheafOfModules.{v} R ⥤ (Cᵒᵖ ⥤ ModuleCat.{v} A) where
  obj M := toBasePresheafObj ψ hψ M
  map {M N} f :=
    { app T := ModuleCat.ofHom
        (X := toBasePresheafObjObj ψ M T) (Y := toBasePresheafObjObj ψ N T)
        { toFun := f.app T
          map_add' := fun x y ↦ (f.app T).hom.map_add x y
          map_smul' := fun a ↦ (f.app T).hom.map_smul (ψ T a) }
      naturality T T' g := by
        ext x
        exact _root_.PresheafOfModules.naturality_apply f g x }

/-- The sections of `toBasePresheaf ψ hψ M` over `T`. -/
@[simp]
lemma toBasePresheaf_obj_obj (M : _root_.PresheafOfModules.{v} R) (T : Cᵒᵖ) :
    ((toBasePresheaf ψ hψ).obj M).obj T = (ModuleCat.restrictScalars (ψ T)).obj (M.obj T) := rfl

/-- The components of `toBasePresheaf` on morphisms, on elements. -/
lemma toBasePresheaf_map_app_apply {M N : _root_.PresheafOfModules.{v} R} (f : M ⟶ N)
    (T : Cᵒᵖ) (x : M.obj T) : (((toBasePresheaf ψ hψ).map f).app T).hom x = f.app T x := rfl

/-- `toBasePresheaf` is additive. -/
instance toBasePresheaf_additive : (toBasePresheaf ψ hψ).Additive where
  map_add := by intros; rfl

/-- Evaluating `toBasePresheaf` at an object is evaluation followed by restriction of
scalars. -/
def toBasePresheafCompEvaluationIso (T : Cᵒᵖ) :
    toBasePresheaf ψ hψ ⋙ (evaluation Cᵒᵖ (ModuleCat.{v} A)).obj T ≅
      _root_.PresheafOfModules.evaluation.{v} R T ⋙ ModuleCat.restrictScalars (ψ T) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl)

/-- **`toBasePresheaf` preserves every limit**: limits of presheaves are computed objectwise,
and restriction of scalars preserves limits. -/
instance preservesLimit_toBasePresheaf {J : Type*} [Category* J]
    (F : J ⥤ _root_.PresheafOfModules.{v} R)
    [∀ T, PreservesLimit F (_root_.PresheafOfModules.evaluation.{v} R T)]
    [∀ T, PreservesLimit (F ⋙ _root_.PresheafOfModules.evaluation.{v} R T)
      (ModuleCat.restrictScalars (ψ T))] :
    PreservesLimit F (toBasePresheaf ψ hψ) := by
  refine preservesLimit_of_evaluation _ _ fun T ↦ ?_
  have : PreservesLimit F
      (_root_.PresheafOfModules.evaluation.{v} R T ⋙ ModuleCat.restrictScalars (ψ T)) :=
    comp_preservesLimit _ _
  exact preservesLimit_of_natIso F (toBasePresheafCompEvaluationIso ψ hψ T).symm

/-! ### The comparison for the cofree presheaf of modules -/

variable [UnivLE.{v₁, v}] (W₀ : Cᵒᵖ) (J : ModuleCat.{v} (R.obj W₀))

/-- The value of the cofree presheaf of modules `cofreeOne W₀ J`, regarded as an `A`-module. -/
abbrev cofreeOneBaseValue : ModuleCat.{v} A :=
  (ModuleCat.restrictScalars (ψ W₀)).obj J

/-- The comparison, for a morphism `g : T ⟶ W₀`, between the value of the plain cofree presheaf
and the factor of `cofreeOne W₀ J` at `g` with its scalars restricted to `A`. -/
def baseCofreeOneFactor {T : Cᵒᵖ} (g : T ⟶ W₀) :
    cofreeOneBaseValue ψ W₀ J ≅
      (ModuleCat.restrictScalars (ψ T)).obj (cofreeOneFactor W₀ J T g) :=
  ModuleCat.restrictScalarsComp'App _ _ _ (hψ g) J

/-- The comparison morphism from the sections of the cofree presheaf of modules, regarded as
`A`-modules, to the plain cofree presheaf. -/
def baseCofreeOneHom (T : Cᵒᵖ) :
    (ModuleCat.restrictScalars (ψ T)).obj (cofreeOneObj W₀ J T) ⟶
      (CechComplex.cofreeOne W₀.unop (cofreeOneBaseValue ψ W₀ J)).obj T :=
  CechComplex.cofreeOneLift W₀.unop (cofreeOneBaseValue ψ W₀ J) fun h ↦
    (ModuleCat.restrictScalars (ψ T)).map (cofreeOneπ W₀ J h.op) ≫
      (baseCofreeOneFactor ψ hψ W₀ J h.op).inv

/-- The components of `baseCofreeOneHom`. -/
@[reassoc]
theorem baseCofreeOneHom_comp_cofreeOneπ (T : Cᵒᵖ) (h : W₀.unop ⟶ T.unop) :
    baseCofreeOneHom ψ hψ W₀ J T ≫
        CechComplex.cofreeOneπ W₀.unop (cofreeOneBaseValue ψ W₀ J) h =
      (ModuleCat.restrictScalars (ψ T)).map (cofreeOneπ W₀ J h.op) ≫
        (baseCofreeOneFactor ψ hψ W₀ J h.op).inv :=
  CechComplex.cofreeOneLift_comp_cofreeOneπ _ _ _ h

/-- `baseCofreeOneHom_comp_cofreeOneπ`, with the index of the projection given separately. -/
@[reassoc]
theorem baseCofreeOneHom_comp_cofreeOneπ' (T : Cᵒᵖ) (h : W₀.unop ⟶ T.unop) (g : T ⟶ W₀)
    (hg : g = h.op) :
    baseCofreeOneHom ψ hψ W₀ J T ≫
        CechComplex.cofreeOneπ W₀.unop (cofreeOneBaseValue ψ W₀ J) h =
      (ModuleCat.restrictScalars (ψ T)).map (cofreeOneπ W₀ J g) ≫
        (baseCofreeOneFactor ψ hψ W₀ J g).inv := by
  subst hg
  exact baseCofreeOneHom_comp_cofreeOneπ ψ hψ W₀ J T h

/-- The comparison morphism from the plain cofree presheaf to the sections of the cofree
presheaf of modules, regarded as `A`-modules. -/
def baseCofreeOneInv (T : Cᵒᵖ) :
    (CechComplex.cofreeOne W₀.unop (cofreeOneBaseValue ψ W₀ J)).obj T ⟶
      (ModuleCat.restrictScalars (ψ T)).obj (cofreeOneObj W₀ J T) :=
  Pi.lift (fun g : T ⟶ W₀ ↦
      CechComplex.cofreeOneπ W₀.unop (cofreeOneBaseValue ψ W₀ J) g.unop ≫
        (baseCofreeOneFactor ψ hψ W₀ J g).hom) ≫
    inv (piComparison (ModuleCat.restrictScalars (ψ T))
      fun g : T ⟶ W₀ ↦ cofreeOneFactor W₀ J T g)

/-- The components of `baseCofreeOneInv`. -/
@[reassoc]
theorem baseCofreeOneInv_comp_map_cofreeOneπ (T : Cᵒᵖ) (g : T ⟶ W₀) :
    baseCofreeOneInv ψ hψ W₀ J T ≫
        (ModuleCat.restrictScalars (ψ T)).map (cofreeOneπ W₀ J g) =
      CechComplex.cofreeOneπ W₀.unop (cofreeOneBaseValue ψ W₀ J) g.unop ≫
        (baseCofreeOneFactor ψ hψ W₀ J g).hom := by
  rw [baseCofreeOneInv, Category.assoc, inv_piComparison_comp_map_π]
  exact Pi.lift_π _ _

/-- `baseCofreeOneInv_comp_map_cofreeOneπ`, with the index of the projection given separately. -/
@[reassoc]
theorem baseCofreeOneInv_comp_map_cofreeOneπ' (T : Cᵒᵖ) (g : T ⟶ W₀)
    (h : W₀.unop ⟶ T.unop) (hh : h = g.unop) :
    baseCofreeOneInv ψ hψ W₀ J T ≫
        (ModuleCat.restrictScalars (ψ T)).map (cofreeOneπ W₀ J g) =
      CechComplex.cofreeOneπ W₀.unop (cofreeOneBaseValue ψ W₀ J) h ≫
        (baseCofreeOneFactor ψ hψ W₀ J g).hom := by
  subst hh
  exact baseCofreeOneInv_comp_map_cofreeOneπ ψ hψ W₀ J T g

/-- **The sections of `cofreeOne W₀ J` over `T`, as `A`-modules, are the sections of the plain
cofree presheaf on `W₀.unop`.** -/
@[simps]
def baseCofreeOneIsoApp (T : Cᵒᵖ) :
    (ModuleCat.restrictScalars (ψ T)).obj (cofreeOneObj W₀ J T) ≅
      (CechComplex.cofreeOne W₀.unop (cofreeOneBaseValue ψ W₀ J)).obj T where
  hom := baseCofreeOneHom ψ hψ W₀ J T
  inv := baseCofreeOneInv ψ hψ W₀ J T
  hom_inv_id := by
    refine (cancel_mono (piComparison (ModuleCat.restrictScalars (ψ T))
      fun g : T ⟶ W₀ ↦ cofreeOneFactor W₀ J T g)).1 (Pi.hom_ext _ _ fun g ↦ ?_)
    rw [Category.assoc, Category.assoc, piComparison_comp_π, Category.id_comp,
      piComparison_comp_π, baseCofreeOneInv_comp_map_cofreeOneπ,
      baseCofreeOneHom_comp_cofreeOneπ'_assoc ψ hψ W₀ J T g.unop g rfl, Iso.inv_hom_id,
      Category.comp_id]
  inv_hom_id := by
    refine CechComplex.cofreeOne_obj_hom_ext W₀.unop (cofreeOneBaseValue ψ W₀ J) fun h ↦ ?_
    rw [Category.assoc, baseCofreeOneHom_comp_cofreeOneπ,
      baseCofreeOneInv_comp_map_cofreeOneπ'_assoc ψ hψ W₀ J T h.op h rfl, Iso.hom_inv_id,
      Category.comp_id, Category.id_comp]

omit [UnivLE.{v₁, v}] in
/-- **The restriction maps of `(toBasePresheaf ψ hψ).obj M` are those of `M`**, read through the
comparison between restricting scalars along `ψ T'` and restricting first along `R.map f` and
then along `ψ T`. -/
theorem toBasePresheaf_obj_map_eq (M : _root_.PresheafOfModules.{v} R) {T T' : Cᵒᵖ}
    (f : T ⟶ T') :
    ((toBasePresheaf ψ hψ).obj M).map f =
      (ModuleCat.restrictScalars (ψ T)).map (M.map f) ≫
        (ModuleCat.restrictScalarsComp'App (ψ T) (R.map f).hom (ψ T') (hψ f) (M.obj T')).inv := by
  ext x
  rfl

/-- **The comparison morphism is natural.** The restriction map `φ` is taken as a separate
argument together with the equation `hφ` describing it, which is `toBasePresheaf_obj_map_eq`. -/
theorem baseCofreeOneHom_naturality {T T' : Cᵒᵖ} (f : T ⟶ T')
    (φ : (ModuleCat.restrictScalars (ψ T)).obj (cofreeOneObj W₀ J T) ⟶
      (ModuleCat.restrictScalars (ψ T')).obj (cofreeOneObj W₀ J T'))
    (hφ : φ = (ModuleCat.restrictScalars (ψ T)).map (cofreeOneMap W₀ J f) ≫
      (ModuleCat.restrictScalarsComp'App (ψ T) (R.map f).hom (ψ T') (hψ f)
        (cofreeOneObj W₀ J T')).inv) :
    φ ≫ baseCofreeOneHom ψ hψ W₀ J T' =
      baseCofreeOneHom ψ hψ W₀ J T ≫
        (CechComplex.cofreeOne W₀.unop (cofreeOneBaseValue ψ W₀ J)).map f := by
  subst hφ
  refine CechComplex.cofreeOne_obj_hom_ext W₀.unop (cofreeOneBaseValue ψ W₀ J) fun h ↦ ?_
  simp only [Category.assoc]
  rw [baseCofreeOneHom_comp_cofreeOneπ, CechComplex.cofreeOne_map_comp_cofreeOneπ,
    baseCofreeOneHom_comp_cofreeOneπ, baseCofreeOneFactor, baseCofreeOneFactor,
    ← ModuleCat.restrictScalarsComp'App_inv_naturality_assoc,
    ← CategoryTheory.Functor.map_comp_assoc,
    cofreeOneMap_comp_cofreeOneπ' W₀ J f h.op ((h ≫ f.unop).op)
      (by rw [op_comp, Quiver.Hom.op_unop]),
    CategoryTheory.Functor.map_comp_assoc]
  refine congrArg ((ModuleCat.restrictScalars (ψ T)).map
    (cofreeOneπ W₀ J ((h ≫ f.unop).op)) ≫ ·) ?_
  ext x
  rfl

/-- **The image of the cofree presheaf of modules `cofreeOne W₀ J` under `toBasePresheaf` is the
plain cofree presheaf on `W₀.unop`** with value `J` regarded as an `A`-module. -/
def toBasePresheafCofreeOneIso :
    (toBasePresheaf ψ hψ).obj (cofreeOne W₀ J) ≅
      CechComplex.cofreeOne W₀.unop (cofreeOneBaseValue ψ W₀ J) :=
  NatIso.ofComponents (baseCofreeOneIsoApp ψ hψ W₀ J) fun {_ _} f ↦
    baseCofreeOneHom_naturality ψ hψ W₀ J f _ (toBasePresheaf_obj_map_eq ψ hψ (cofreeOne W₀ J) f)

end Stacks.CategoryTheory.PresheafOfModules

end
