module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EssentiallySmallInternalHom

/-!
# A sectionwise model of coextension of scalars on an essentially small ringed site

Let `X` be a ringed site, let `ψ : 𝒪_X ⟶ 𝒜` be a morphism of sheaves of rings with `𝒜`
commutative, and let `ℱ` be an `𝒪_X`-module.  The internal Hom `𝓗om_{𝒪_X}(𝒜, ℱ)` of
`AlgebraicGeometry.RingedSite.internalHomSheaf` — whose sections over `U` are the `𝒪_X|_U`-linear
maps `𝒜|_U ⟶ ℱ|_U` on the slice site `X/U` — carries a second module structure, over `𝒜`:

`(a · h)(b) = h(a b)`,

precomposition with multiplication by `a`.  This file constructs that `𝒜`-module, descends it to
the module universe of `𝒜` when the site is essentially small, and constructs the evaluation

`τ : 𝓗om_{𝒪_X}(𝒜, ℱ) ⟶ ℱ`,  `h ↦ h(1)`,

as a morphism of `𝒪_X`-modules, together with the formula `τ(a · h) = h(a)`.

This is the sectionwise model of the coextension of scalars of Stacks 0932 at the universes of the
small étale site of an algebraic space, where the objects of the site lie one universe above its
morphisms and its rings.  It is not a second construction of the coextension functor: no
adjunction is claimed for it.  Its use is as a *test object* for an abstractly produced right
adjoint of restriction of scalars: an `𝒪_X`-linear map out of the restriction of an `𝒜`-module
determines an `𝒜`-linear map into that right adjoint, and the formula `τ(a · h) = h(a)` makes the
image of such a map computable on sections.

## Main definitions

* `AlgebraicGeometry.RingedSite.coextensionBase`: `𝒜` read as an `𝒪_X`-module through `ψ`.
* `AlgebraicGeometry.RingedSite.coextensionMul`: multiplication by a section of `𝒜` on the
  restriction of `𝒜` to a slice, as an endomorphism of `𝒪_X|_U`-modules.
* `AlgebraicGeometry.RingedSite.coextensionModelLift`: the `𝒜`-module `𝓗om_{𝒪_X}(𝒜, ℱ)`, with
  sections in the universe of the internal Hom.
* `AlgebraicGeometry.RingedSite.coextensionModel`: the same with sections in the module universe
  of `𝒜`, on an essentially small site.
* `AlgebraicGeometry.RingedSite.coextensionModelEval`: the evaluation `h ↦ h(1)`.

## Main results

* `AlgebraicGeometry.RingedSite.coextensionModelEval_app_smul`: `τ(a · h) = h(a)`.

## References

* [Stacks Project, Tag 0932](https://stacks.math.columbia.edu/tag/0932)
* [Stacks Project, Tag 03EM](https://stacks.math.columbia.edu/tag/03EM)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u v w

namespace AlgebraicGeometry.RingedSite

variable (X : RingedSite.{u, v, w}) {R : Sheaf X.J RingCat.{w}}
  (ψ : Stacks.SheafOfModules.Tensor.ringSheaf X.O ⟶ R)
  (hR : ∀ (U : X.Cᵒᵖ) (a b : R.obj.obj U), a * b = b * a)

/-- **`𝒜` read as an `𝒪_X`-module** through the morphism of sheaves of rings `ψ : 𝒪_X ⟶ 𝒜`. -/
abbrev coextensionBase : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) :=
  (SheafOfModules.restrictScalars ψ).obj (SheafOfModules.unit R)

/-- A section of `𝒜` over an object of a slice of the site, read as a section of the
`𝒪_X`-module `coextensionBase`. -/
abbrev coextensionBaseSection {U : X.C} (Z : (Over U)ᵒᵖ) (a : R.obj.obj (op Z.unop.left)) :
    ((restrFun X.O.obj U).obj (valOf X (coextensionBase X ψ))).obj Z := a

/-- The restriction to an object `Z` of the slice `X/U` of a section `a ∈ 𝒜(U)`. -/
abbrev coextensionRestr {U : X.C} (a : R.obj.obj (op U)) (Z : (Over U)ᵒᵖ) :
    R.obj.obj (op Z.unop.left) :=
  (R.obj.map Z.unop.hom.op).hom a

omit hR in
/-- Restricting `coextensionRestr X a Z` along a morphism `Z ⟶ Z'` of the slice `X/U` gives
`coextensionRestr X a Z'`. -/
theorem coextensionRestr_map {U : X.C} (a : R.obj.obj (op U)) {Z Z' : (Over U)ᵒᵖ}
    (g : Z ⟶ Z') :
    (R.obj.map ((Over.forget U).map g.unop).op).hom (coextensionRestr X a Z) =
      coextensionRestr X a Z' := by
  dsimp only [coextensionRestr]
  rw [← RingCat.comp_apply, ← R.obj.map_comp, ← op_comp]
  exact congrArg (fun h => (R.obj.map h.op).hom a) (Over.w g.unop)

/-- Multiplication by the restriction of a section `a ∈ 𝒜(U)` on the sections of `𝒜|_U` over an
object `Z` of the slice `X/U`, as an `𝒪_X(Z)`-linear map.  It is `𝒪_X`-linear because `𝒜` is
commutative and `𝒪_X` acts on `𝒜` through the ring map `ψ`. -/
def coextensionMulApp {U : X.C} (a : R.obj.obj (op U)) (Z : (Over U)ᵒᵖ) :
    ((restrFun X.O.obj U).obj (valOf X (coextensionBase X ψ))).obj Z ⟶
      ((restrFun X.O.obj U).obj (valOf X (coextensionBase X ψ))).obj Z :=
  ModuleCat.homAddEquiv.symm
    { toFun := fun x => coextensionBaseSection X ψ Z
        (coextensionRestr X a Z * (show R.obj.obj (op Z.unop.left) from x))
      map_add' := fun x y => mul_add (coextensionRestr X a Z)
        (show R.obj.obj (op Z.unop.left) from x) (show R.obj.obj (op Z.unop.left) from y)
      map_smul' := fun r x => by
        change coextensionRestr X a Z * ((ψ.hom.app (op Z.unop.left)).hom r *
            (show R.obj.obj (op Z.unop.left) from x)) =
          (ψ.hom.app (op Z.unop.left)).hom r *
            (coextensionRestr X a Z * (show R.obj.obj (op Z.unop.left) from x))
        rw [← mul_assoc, ← mul_assoc, hR _ (coextensionRestr X a Z)] }

/-- **Multiplication by a section `a ∈ 𝒜(U)`** on the restriction of the `𝒪_X`-module `𝒜` to the
slice `X/U`, as an endomorphism of `𝒪_X|_U`-modules. -/
def coextensionMul {U : X.C} (a : R.obj.obj (op U)) :
    (restrFun X.O.obj U).obj (valOf X (coextensionBase X ψ)) ⟶
      (restrFun X.O.obj U).obj (valOf X (coextensionBase X ψ)) where
  app Z := coextensionMulApp X ψ hR a Z
  naturality {Z Z'} g := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro x
    change coextensionRestr X a Z' * (show R.obj.obj (op Z'.unop.left) from
        (R.obj.map ((Over.forget U).map g.unop).op).hom (show R.obj.obj (op Z.unop.left) from x)) =
      (R.obj.map ((Over.forget U).map g.unop).op).hom
        (coextensionRestr X a Z * (show R.obj.obj (op Z.unop.left) from x))
    rw [map_mul, coextensionRestr_map]

/-- Multiplication by `a` sends a section `x` of `𝒜|_U` over `Z` to the restriction of `a` to `Z`
times `x`. -/
@[simp]
theorem coextensionMul_app_apply {U : X.C} (a : R.obj.obj (op U)) (Z : (Over U)ᵒᵖ)
    (x : ((restrFun X.O.obj U).obj (valOf X (coextensionBase X ψ))).obj Z) :
    ((coextensionMul X ψ hR a).app Z).hom x =
      coextensionBaseSection X ψ Z
        (coextensionRestr X a Z * (show R.obj.obj (op Z.unop.left) from x)) := rfl

/-! ### The `𝒜`-module structure on the internal Hom -/

omit hR in
/-- The restriction of `1` is `1`. -/
theorem coextensionRestr_one {U : X.C} (Z : (Over U)ᵒᵖ) :
    coextensionRestr X (1 : R.obj.obj (op U)) Z = 1 := map_one _

omit hR in
/-- Restriction to the slice is multiplicative. -/
theorem coextensionRestr_mul {U : X.C} (a b : R.obj.obj (op U)) (Z : (Over U)ᵒᵖ) :
    coextensionRestr X (a * b) Z = coextensionRestr X a Z * coextensionRestr X b Z :=
  map_mul _ _ _

omit hR in
/-- Restriction to the slice is additive. -/
theorem coextensionRestr_add {U : X.C} (a b : R.obj.obj (op U)) (Z : (Over U)ᵒᵖ) :
    coextensionRestr X (a + b) Z = coextensionRestr X a Z + coextensionRestr X b Z :=
  map_add _ _ _

omit hR in
/-- The restriction of `0` is `0`. -/
theorem coextensionRestr_zero {U : X.C} (Z : (Over U)ᵒᵖ) :
    coextensionRestr X (0 : R.obj.obj (op U)) Z = 0 := map_zero _

/-- Two morphisms of presheaves of modules agreeing on all elements are equal. -/
private theorem hom_ext_of_apply_eq {C : Type*} [Category C] {S : Cᵒᵖ ⥤ RingCat}
    {P Q : PresheafOfModules S} (f g : P ⟶ Q) (h : ∀ Z x, (f.app Z).hom x = (g.app Z).hom x) :
    f = g :=
  PresheafOfModules.hom_ext fun Z => ModuleCat.hom_ext (LinearMap.ext (h Z))

/-- Multiplication by `1` is the identity. -/
theorem coextensionMul_one {U : X.C} :
    coextensionMul X ψ hR (1 : R.obj.obj (op U)) = 𝟙 _ := by
  refine hom_ext_of_apply_eq _ _ fun Z x => ?_
  change coextensionRestr X (1 : R.obj.obj (op U)) Z * (show R.obj.obj (op Z.unop.left) from x) =
    (show R.obj.obj (op Z.unop.left) from x)
  rw [coextensionRestr_one, one_mul]

/-- Multiplication by `a * b` is multiplication by `a` followed by multiplication by `b`. -/
theorem coextensionMul_mul {U : X.C} (a b : R.obj.obj (op U)) :
    coextensionMul X ψ hR (a * b) = coextensionMul X ψ hR a ≫ coextensionMul X ψ hR b := by
  refine hom_ext_of_apply_eq _ _ fun Z x => ?_
  change coextensionRestr X (a * b) Z * (show R.obj.obj (op Z.unop.left) from x) =
    coextensionRestr X b Z * (coextensionRestr X a Z * (show R.obj.obj (op Z.unop.left) from x))
  rw [coextensionRestr_mul, ← mul_assoc, hR _ (coextensionRestr X b Z)]

/-- Multiplication by `a + b` is the sum of multiplication by `a` and by `b`. -/
theorem coextensionMul_add {U : X.C} (a b : R.obj.obj (op U)) :
    coextensionMul X ψ hR (a + b) = coextensionMul X ψ hR a + coextensionMul X ψ hR b := by
  refine hom_ext_of_apply_eq _ _ fun Z x => ?_
  change coextensionRestr X (a + b) Z * (show R.obj.obj (op Z.unop.left) from x) =
    coextensionRestr X a Z * (show R.obj.obj (op Z.unop.left) from x) +
      coextensionRestr X b Z * (show R.obj.obj (op Z.unop.left) from x)
  rw [coextensionRestr_add, add_mul]

/-- Multiplication by `0` is the zero morphism. -/
theorem coextensionMul_zero {U : X.C} :
    coextensionMul X ψ hR (0 : R.obj.obj (op U)) = 0 := by
  refine hom_ext_of_apply_eq _ _ fun Z x => ?_
  change coextensionRestr X (0 : R.obj.obj (op U)) Z * (show R.obj.obj (op Z.unop.left) from x) =
    (0 : R.obj.obj (op Z.unop.left))
  rw [coextensionRestr_zero, zero_mul]

variable (F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))

/-- **The `𝒜(U)`-module structure on `Hom_{𝒪_X|_U}(𝒜|_U, ℱ|_U)`**: `a · h` is `h` precomposed with
multiplication by `a`. -/
@[reducible] def coextensionHomModule (U : X.C) :
    Module (R.obj.obj (op U))
      ((restrFun X.O.obj U).obj (valOf X (coextensionBase X ψ)) ⟶
        (restrFun X.O.obj U).obj (valOf X F)) where
  smul a h := coextensionMul X ψ hR a ≫ h
  one_smul h := by
    change coextensionMul X ψ hR 1 ≫ h = h
    rw [coextensionMul_one, Category.id_comp]
  mul_smul a b h := by
    change coextensionMul X ψ hR (a * b) ≫ h =
      coextensionMul X ψ hR a ≫ coextensionMul X ψ hR b ≫ h
    rw [coextensionMul_mul, Category.assoc]
  smul_zero a := Limits.comp_zero
  smul_add a h h' := Preadditive.comp_add _ _ _ _ _ _
  add_smul a b h := by
    change coextensionMul X ψ hR (a + b) ≫ h =
      coextensionMul X ψ hR a ≫ h + coextensionMul X ψ hR b ≫ h
    rw [coextensionMul_add, Preadditive.add_comp]
  zero_smul h := by
    change coextensionMul X ψ hR 0 ≫ h = 0
    rw [coextensionMul_zero, Limits.zero_comp]

/-- Restricting multiplication by `a` along `f : V ⟶ U` is multiplication by the restriction of
`a`. -/
theorem homRestr_coextensionMul {V U : X.C} (f : V ⟶ U) (a : R.obj.obj (op U)) :
    homRestr X.O.obj (valOf X (coextensionBase X ψ)) (valOf X (coextensionBase X ψ)) f
        (coextensionMul X ψ hR a) =
      coextensionMul X ψ hR ((R.obj.map f.op).hom a) := by
  refine hom_ext_of_apply_eq _ _ fun W x => ?_
  change (show R.obj.obj (op W.unop.left) from coextensionRestr X a ((Over.map f).op.obj W)) *
      (show R.obj.obj (op W.unop.left) from x) =
    coextensionRestr X ((R.obj.map f.op).hom a) W * (show R.obj.obj (op W.unop.left) from x)
  congr 1
  change (R.obj.map (W.unop.hom ≫ f).op).hom a = (R.obj.map W.unop.hom.op).hom
    ((R.obj.map f.op).hom a)
  rw [op_comp, Functor.map_comp, RingCat.comp_apply]

/-- Restriction along `f : V ⟶ U` of the composite of two local morphisms is the composite of the
restrictions. -/
theorem homRestr_comp_comp {V U : X.C} (f : V ⟶ U) {A B C : SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (β : (restrFun X.O.obj U).obj (valOf X A) ⟶ (restrFun X.O.obj U).obj (valOf X B))
    (γ : (restrFun X.O.obj U).obj (valOf X B) ⟶ (restrFun X.O.obj U).obj (valOf X C)) :
    homRestr X.O.obj (valOf X A) (valOf X C) f (β ≫ γ) =
      homRestr X.O.obj (valOf X A) (valOf X B) f β ≫
        homRestr X.O.obj (valOf X B) (valOf X C) f γ := by
  rw [homRestr, homRestr, homRestr, Functor.map_comp]
  simp only [Category.assoc, eqToHom_trans_assoc, eqToHom_refl, Category.id_comp]

/-- **The internal Hom `𝓗om_{𝒪_X}(𝒜, ℱ)` as a presheaf of `𝒜`-modules**, `(a · h)(b) = h(a b)`. -/
def coextensionModelPresheaf : PresheafOfModules.{max u v w} R.obj :=
  letI : ∀ U : X.Cᵒᵖ, Module (R.obj.obj U)
      ((internalHom X.O.obj (valOf X (coextensionBase X ψ)) (valOf X F)).presheaf.obj U) :=
    fun U => coextensionHomModule X ψ hR F U.unop
  PresheafOfModules.ofPresheaf
    (internalHom X.O.obj (valOf X (coextensionBase X ψ)) (valOf X F)).presheaf
    (fun {U U'} f a h => by
      let h' : (restrFun X.O.obj U.unop).obj (valOf X (coextensionBase X ψ)) ⟶
          (restrFun X.O.obj U.unop).obj (valOf X F) := h
      change homRestr X.O.obj (valOf X (coextensionBase X ψ)) (valOf X F) f.unop
          (coextensionMul X ψ hR a ≫ h') =
        coextensionMul X ψ hR ((R.obj.map f).hom a) ≫
          homRestr X.O.obj (valOf X (coextensionBase X ψ)) (valOf X F) f.unop h'
      rw [homRestr_comp_comp, homRestr_coextensionMul]
      rfl)

/-- **The `𝒜`-module `𝓗om_{𝒪_X}(𝒜, ℱ)`**, with sections in the universe of the internal Hom.  Its
underlying presheaf of abelian groups is that of
`AlgebraicGeometry.RingedSite.internalHomSheaf`, whose sheaf condition it inherits. -/
def coextensionModelLift : SheafOfModules.{max u v w} R where
  val := coextensionModelPresheaf X ψ hR F
  isSheaf := (internalHomSheaf X (coextensionBase X ψ) F).isSheaf

/-! ### Descent to the module universe of `𝒜`, and the evaluation -/

section Small

variable [EssentiallySmall.{w} X.C]

/-- The sections of `AlgebraicGeometry.RingedSite.coextensionModelLift` over each object are
`w`-small. -/
instance small_coextensionModelLift_obj (U : X.Cᵒᵖ) :
    Small.{w} ((coextensionModelLift X ψ hR F).val.obj U) :=
  inferInstanceAs (Small.{w} ((internalHomSheaf X (coextensionBase X ψ) F).val.obj U))

/-- **The `𝒜`-module `𝓗om_{𝒪_X}(𝒜, ℱ)` with sections in the module universe of `𝒜`**, on an
essentially small ringed site: `AlgebraicGeometry.RingedSite.coextensionModelLift` with its
sections shrunk, as `AlgebraicGeometry.RingedSite.internalHomSheafSmall` shrinks the internal
Hom. -/
def coextensionModel : SheafOfModules.{w} R :=
  Stacks.SheafOfModules.sheafShrink.{w, max u v} R (coextensionModelLift X ψ hR F)

/-- A section of `AlgebraicGeometry.RingedSite.coextensionModel` over `U`, read as the
`𝒪_X|_U`-linear map `𝒜|_U ⟶ ℱ|_U` it is. -/
def coextensionModelHom {U : X.C} (m : (coextensionModel X ψ hR F).val.obj (op U)) :
    (restrFun X.O.obj U).obj (valOf X (coextensionBase X ψ)) ⟶
      (restrFun X.O.obj U).obj (valOf X F) :=
  Shrink.addEquiv (α := ((coextensionModelLift X ψ hR F).val.presheaf.obj (op U) : Type _)) m

/-- Every local morphism `𝒜|_U ⟶ ℱ|_U` is a section of the model. -/
def coextensionModelMk {U : X.C}
    (h : (restrFun X.O.obj U).obj (valOf X (coextensionBase X ψ)) ⟶
      (restrFun X.O.obj U).obj (valOf X F)) :
    (coextensionModel X ψ hR F).val.obj (op U) :=
  (Shrink.addEquiv (α := ((coextensionModelLift X ψ hR F).val.presheaf.obj (op U) : Type _))).symm h

/-- The local morphism of the section attached to `h` is `h`. -/
@[simp]
theorem coextensionModelHom_mk {U : X.C}
    (h : (restrFun X.O.obj U).obj (valOf X (coextensionBase X ψ)) ⟶
      (restrFun X.O.obj U).obj (valOf X F)) :
    coextensionModelHom X ψ hR F (coextensionModelMk X ψ hR F h) = h :=
  (Shrink.addEquiv
    (α := ((coextensionModelLift X ψ hR F).val.presheaf.obj (op U) : Type _))).apply_symm_apply h

/-- The action of `𝒜` on the model is precomposition with multiplication. -/
theorem coextensionModelHom_smul {U : X.C} (a : R.obj.obj (op U))
    (m : (coextensionModel X ψ hR F).val.obj (op U)) :
    coextensionModelHom X ψ hR F (a • m) =
      coextensionMul X ψ hR a ≫ coextensionModelHom X ψ hR F m :=
  Stacks.SheafOfModules.shrinkPresheaf_addEquiv_smul R.obj (coextensionModelLift X ψ hR F).val
    (op U) a m

/-- The identity of `U` as an object of the slice `X/U`. -/
abbrev overId (U : X.C) : (Over U)ᵒᵖ := op (Over.mk (𝟙 U))

/-- The value at `1` of a local morphism `𝒜|_U ⟶ ℱ|_U`. -/
def coextensionEvalOne {U : X.C}
    (h : (restrFun X.O.obj U).obj (valOf X (coextensionBase X ψ)) ⟶
      (restrFun X.O.obj U).obj (valOf X F)) : F.val.obj (op U) :=
  (h.app (overId X U)).hom (coextensionBaseSection X ψ (overId X U) 1)

omit [EssentiallySmall.{w} X.C] in
/-- Evaluation at `1` commutes with restriction. -/
theorem coextensionEvalOne_homRestr {V U : X.C} (f : V ⟶ U)
    (h : (restrFun X.O.obj U).obj (valOf X (coextensionBase X ψ)) ⟶
      (restrFun X.O.obj U).obj (valOf X F)) :
    coextensionEvalOne X ψ F (homRestr X.O.obj (valOf X (coextensionBase X ψ)) (valOf X F) f h) =
      (F.val.map f.op).hom (coextensionEvalOne X ψ F h) := by
  let k : (Over.map f).obj (Over.mk (𝟙 V)) ⟶ Over.mk (𝟙 U) := Over.homMk f (by simp)
  have h1 : (((restrFun X.O.obj U).obj (valOf X (coextensionBase X ψ))).map k.op).hom
      (coextensionBaseSection X ψ (overId X U) 1) =
        coextensionBaseSection X ψ (op ((Over.map f).obj (Over.mk (𝟙 V)))) 1 :=
    map_one (R.obj.map f.op).hom
  change ((h.app (op ((Over.map f).obj (Over.mk (𝟙 V))))).hom
      (coextensionBaseSection X ψ (op ((Over.map f).obj (Over.mk (𝟙 V)))) 1)) = _
  rw [← h1]
  exact congrArg (fun φ => φ.hom (coextensionBaseSection X ψ (overId X U) 1)) (h.naturality k.op)

/-- Reading a section of the model as a local morphism is additive. -/
theorem coextensionModelHom_add {U : X.C} (m m' : (coextensionModel X ψ hR F).val.obj (op U)) :
    coextensionModelHom X ψ hR F (m + m') =
      coextensionModelHom X ψ hR F m + coextensionModelHom X ψ hR F m' :=
  map_add (Shrink.addEquiv (α := ((coextensionModelLift X ψ hR F).val.presheaf.obj (op U) :
    Type _))) m m'

omit [EssentiallySmall.{w} X.C] in
/-- Evaluation at `1` is additive. -/
theorem coextensionEvalOne_add {U : X.C}
    (h h' : (restrFun X.O.obj U).obj (valOf X (coextensionBase X ψ)) ⟶
      (restrFun X.O.obj U).obj (valOf X F)) :
    coextensionEvalOne X ψ F (h + h') = coextensionEvalOne X ψ F h + coextensionEvalOne X ψ F h' :=
  rfl

/-- **The evaluation `h ↦ h(1)`** at one object, as a linear map. -/
def coextensionModelEvalApp (U : X.Cᵒᵖ) :
    ((SheafOfModules.restrictScalars ψ).obj (coextensionModel X ψ hR F)).val.obj U ⟶
      F.val.obj U :=
  ModuleCat.homAddEquiv.symm
    { toFun := fun (m : ((SheafOfModules.restrictScalars ψ).obj
          (coextensionModel X ψ hR F)).val.obj U) =>
        coextensionEvalOne X ψ F (coextensionModelHom X ψ hR F (U := U.unop)
          (show (coextensionModel X ψ hR F).val.obj (op U.unop) from m))
      map_add' := fun m m' => by
        change coextensionEvalOne X ψ F (coextensionModelHom X ψ hR F (U := U.unop)
            ((show (coextensionModel X ψ hR F).val.obj (op U.unop) from m) +
              (show (coextensionModel X ψ hR F).val.obj (op U.unop) from m'))) = _
        rw [coextensionModelHom_add, coextensionEvalOne_add]
      map_smul' := fun r m => by
        change coextensionEvalOne X ψ F (coextensionModelHom X ψ hR F (U := U.unop)
            ((ψ.hom.app U).hom r •
              (show (coextensionModel X ψ hR F).val.obj (op U.unop) from m))) =
          r • coextensionEvalOne X ψ F (coextensionModelHom X ψ hR F (U := U.unop)
            (show (coextensionModel X ψ hR F).val.obj (op U.unop) from m))
        rw [coextensionModelHom_smul]
        dsimp only [coextensionEvalOne]
        rw [PresheafOfModules.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply,
          coextensionMul_app_apply]
        have key : coextensionBaseSection X ψ (overId X U.unop)
            (coextensionRestr X ((ψ.hom.app U).hom r) (overId X U.unop) *
              (show R.obj.obj (op (Over.mk (𝟙 U.unop)).left) from
                coextensionBaseSection X ψ (overId X U.unop) 1)) =
            (show (ORestr X.O.obj U.unop).obj (overId X U.unop) from r) •
              coextensionBaseSection X ψ (overId X U.unop) 1 := by
          change (R.obj.map (𝟙 U.unop).op).hom ((ψ.hom.app U).hom r) * 1 =
            (ψ.hom.app U).hom r * 1
          rw [op_id, CategoryTheory.Functor.map_id]
          rfl
        rw [key, map_smul]
        rfl }

/-- **The evaluation `τ : 𝓗om_{𝒪_X}(𝒜, ℱ) ⟶ ℱ`, `h ↦ h(1)`**, as a morphism of `𝒪_X`-modules out
of the restriction of scalars of the model. -/
def coextensionModelEval :
    (SheafOfModules.restrictScalars ψ).obj (coextensionModel X ψ hR F) ⟶ F where
  val :=
    { app U := coextensionModelEvalApp X ψ hR F U
      naturality {U U'} f := by
        ext m
        change coextensionEvalOne X ψ F (coextensionModelHom X ψ hR F (U := U'.unop)
            ((coextensionModel X ψ hR F).val.map f m)) =
          (F.val.map f).hom (coextensionEvalOne X ψ F (coextensionModelHom X ψ hR F m))
        have hmap : coextensionModelHom X ψ hR F (U := U'.unop)
            ((coextensionModel X ψ hR F).val.map f m) =
            homRestr X.O.obj (valOf X (coextensionBase X ψ)) (valOf X F) f.unop
              (coextensionModelHom X ψ hR F m) :=
          Stacks.shrinkPresheaf_map_apply _ f m
        rw [hmap, coextensionEvalOne_homRestr]
        rfl }

/-- **`τ(a · h) = h(a)`**: the evaluation of the action of `a ∈ 𝒜(U)` on a section of the model is
the value at `a` of the local morphism it is. -/
theorem coextensionModelEval_app_smul (U : X.C) (a : R.obj.obj (op U))
    (m : (coextensionModel X ψ hR F).val.obj (op U)) :
    ((coextensionModelEval X ψ hR F).val.app (op U)).hom (a • m) =
      ((coextensionModelHom X ψ hR F m).app (overId X U)).hom
        (coextensionBaseSection X ψ (overId X U) a) := by
  change coextensionEvalOne X ψ F (coextensionModelHom X ψ hR F (a • m)) = _
  rw [coextensionModelHom_smul]
  dsimp only [coextensionEvalOne]
  rw [PresheafOfModules.comp_app, ModuleCat.hom_comp, LinearMap.comp_apply,
    coextensionMul_app_apply]
  congr 1
  change (R.obj.map (𝟙 U).op).hom a * 1 = a
  rw [op_id, CategoryTheory.Functor.map_id, mul_one]
  rfl

/-- **`τ(a · h) = h(a)`** for the section of the model attached to a local morphism `h`. -/
theorem coextensionModelEval_app_smul_mk (U : X.C) (a : R.obj.obj (op U))
    (h : (restrFun X.O.obj U).obj (valOf X (coextensionBase X ψ)) ⟶
      (restrFun X.O.obj U).obj (valOf X F)) :
    ((coextensionModelEval X ψ hR F).val.app (op U)).hom (a • coextensionModelMk X ψ hR F h) =
      (h.app (overId X U)).hom (coextensionBaseSection X ψ (overId X U) a) := by
  rw [coextensionModelEval_app_smul, coextensionModelHom_mk]

end Small

/-- The restriction of a section along the identity is the section itself. -/
private theorem map_op_id_apply {C : Type*} [Category C] {S : Cᵒᵖ ⥤ RingCat}
    (M : PresheafOfModules S) {U : C} (x : M.obj (op U)) : (M.map (𝟙 U).op).hom x = x :=
  (PresheafOfModules.congr_map_apply M op_id x).trans (by rw [M.map_id]; rfl)

/-! ### The local morphism `𝒪|_U ⟶ 𝒩|_U` attached to a section -/

section SectionHom

variable {N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}

/-- **The local morphism `𝒪_X|_U ⟶ 𝒩|_U`, `r ↦ r · f`**, attached to a section `f ∈ 𝒩(U)`. -/
def restrFunSectionHom {U : X.C} (f : N.val.obj (op U)) :
    (restrFun X.O.obj U).obj
        (valOf X (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) ⟶
      (restrFun X.O.obj U).obj (valOf X N) where
  app Z := ModuleCat.homAddEquiv.symm
    { toFun := fun r => (show N.val.obj (op Z.unop.left) from
        (show (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op Z.unop.left) from r) •
          (N.val.map Z.unop.hom.op).hom f)
      map_add' := fun r r' =>
        add_smul (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op Z.unop.left))
          (M := N.val.obj (op Z.unop.left)) _ _ _
      map_smul' := fun r r' =>
        mul_smul (α := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op Z.unop.left))
          (β := N.val.obj (op Z.unop.left)) _ _ _ }
  naturality {Z Z'} k := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro r
    have key := N.val.map_smul ((Over.forget U).map k.unop).op
      (show (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op Z.unop.left) from r)
      ((N.val.map Z.unop.hom.op).hom f)
    have hc : (N.val.map ((Over.forget U).map k.unop).op).hom ((N.val.map Z.unop.hom.op).hom f) =
        (N.val.map Z'.unop.hom.op).hom f := by
      have e : (N.val.map (Z.unop.hom.op ≫ ((Over.forget U).map k.unop).op)).hom f =
          (N.val.map ((Over.forget U).map k.unop).op).hom ((N.val.map Z.unop.hom.op).hom f) := by
        rw [N.val.map_comp]
        rfl
      have hw : Z.unop.hom.op ≫ ((Over.forget U).map k.unop).op = Z'.unop.hom.op := by
        rw [← op_comp]
        exact congrArg Quiver.Hom.op (Over.w k.unop)
      exact e.symm.trans (PresheafOfModules.congr_map_apply N.val hw f)
    rwa [hc, eq_comm] at key

/-- The local morphism `r ↦ r · f` sends `1` over `U` to `f`. -/
theorem restrFunSectionHom_app_overId_one {U : X.C} (f : N.val.obj (op U)) :
    ((restrFunSectionHom X f).app (overId X U)).hom
        (show (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U) from 1) = f := by
  change (1 : (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U)) •
      (show N.val.obj (op U) from (N.val.map (𝟙 U).op).hom f) = f
  rw [one_smul]
  exact map_op_id_apply N.val f

/-- A local morphism `𝒜|_U ⟶ 𝒪|_U` followed by `r ↦ r · f`, evaluated at the identity of `U` on a
section with value `1`, is `f`. -/
theorem restrFun_map_comp_restrFunSectionHom_app_overId {U : X.C}
    {A : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (p : A ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (f : N.val.obj (op U)) (x : A.val.obj (op U))
    (hx : (p.val.app (op U)).hom x =
      (show (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op U) from 1)) :
    (((restrFun X.O.obj U).map (homOf X p) ≫ restrFunSectionHom X f).app (overId X U)).hom x =
      f := by
  change ((restrFunSectionHom X f).app (overId X U)).hom ((p.val.app (op U)).hom x) = f
  rw [hx]
  exact restrFunSectionHom_app_overId_one X f

end SectionHom

/-- A local morphism evaluated at the identity of `U` agrees with its value at the image of the
identity under a functor of slices, `F.map (𝟙 W)` being `𝟙 (F.obj W)` only propositionally. -/
theorem app_overId_eq_app_mk_map_id {D : Type*} [Category D] (F : D ⥤ X.C) (W : D)
    {A B : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (h : (restrFun X.O.obj (F.obj W)).obj (valOf X A) ⟶
      (restrFun X.O.obj (F.obj W)).obj (valOf X B))
    (x : A.val.obj (op (F.obj W))) :
    (h.app (overId X (F.obj W))).hom x = (h.app (op (Over.mk (F.map (𝟙 W))))).hom x := by
  let k : Over.mk (𝟙 (F.obj W)) ⟶ Over.mk (F.map (𝟙 W)) := Over.homMk (𝟙 _) (by simp)
  have hk := congrArg (fun φ => φ.hom x) (h.naturality k.op)
  change (h.app (overId X (F.obj W))).hom ((A.val.map (𝟙 (F.obj W)).op).hom x) =
    (B.val.map (𝟙 (F.obj W)).op).hom ((h.app (op (Over.mk (F.map (𝟙 W))))).hom x) at hk
  rw [map_op_id_apply A.val] at hk
  exact hk.trans (map_op_id_apply B.val _)

end AlgebraicGeometry.RingedSite
