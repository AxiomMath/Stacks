module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Colimits
public import Mathlib.Algebra.Module.Shrink
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.PresheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Generator.Basic
public import Mathlib.CategoryTheory.Presentable.Adjunction
public import Mathlib.CategoryTheory.Sites.Abelian
import StacksCore.Tactic.StacksAttribute

/-!
# Grothendieck abelianness of sheaves of modules in a universe containing the site

Let `C` be a category with a Grothendieck topology `J` and let `R` be a sheaf of rings on
`(C, J)`. The category of sheaves of `R`-modules with sections in a universe `v` is
Grothendieck abelian as soon as the objects, the morphisms and the rings of the site all fit
inside `v`, expressed by three `UnivLE` hypotheses.

## Main results

* `Stacks.SheafOfModules.Small.locallySmall_presheafOfModules` and
  `Stacks.SheafOfModules.Small.locallySmall_sheafOfModules`: the hom types are `v`-small.
* `Stacks.SheafOfModules.Small.hasSeparator_presheafOfModules`: presheaves of modules have a
  separator, the coproduct of the free modules on the shrunken representables.
* `Stacks.SheafOfModules.Small.isGrothendieckAbelian_presheafOfModules` and
  `Stacks.SheafOfModules.Small.isGrothendieckAbelian_sheafOfModules`: presheaves and sheaves
  of modules form Grothendieck abelian categories.

## Implementation notes

The module universe is a variable `v` constrained only by `UnivLE`, rather than the literal
maximum `max u v r w`; the two are different universe expressions even when every `UnivLE`
holds, so `Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck` does not apply.

The separating family is the usual one: for an object `X` of the site, the free module on the
representable `Y ↦ (Y ⟶ X)`. Two of its ingredients leave the module universe, and each is
brought back by `Shrink`:

* the index set `Y.unop ⟶ X` lies in the morphism universe `w`, so the basis is
  `Shrink.{v} (Y.unop ⟶ X)`;
* the coefficients lie in the ring universe `r`, so the coefficient module is
  `Shrink.{v} (R.obj Y)`, which is a module over `R.obj Y` by transport along
  `Shrink.addEquiv`. Taking `Finsupp` of two `v`-types then stays in `v`, so no third
  shrinking is needed, and in particular the sections are a genuine `Finsupp` rather than a
  shrunken one.

The separating family must be indexed by a `v`-small type for its coproduct to exist, so it is
indexed by `Shrink.{v} C` rather than by `C`.

The sheaf-level statements are transported from the presheaf side along the sheafification
adjunction.

## References

* [Stacks Project, Tag 03DB](https://stacks.math.columbia.edu/tag/03DB)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.SheafOfModules.Small

universe u v w r

section FreeMap

/-- The additive map of finitely supported functions induced by a map of index sets and an
additive map of coefficients. -/
def freeMap {I K M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    (g : I → K) (ψ : M →+ N) : (I →₀ M) →+ (K →₀ N) :=
  (Finsupp.mapDomain.addMonoidHom g).comp (Finsupp.mapRange.addMonoidHom ψ)

/-- `freeMap g ψ` sends `Finsupp.single i m` to `Finsupp.single (g i) (ψ m)`. -/
@[simp]
lemma freeMap_single {I K M N : Type*} [AddCommMonoid M] [AddCommMonoid N]
    (g : I → K) (ψ : M →+ N) (i : I) (m : M) :
    freeMap g ψ (Finsupp.single i m) = Finsupp.single (g i) (ψ m) := by
  simp [freeMap, Finsupp.mapDomain_single]

/-- An additive map out of finitely supported functions is semilinear as soon as it is on
`Finsupp.single`s. -/
private lemma finsupp_addMonoidHom_smul {A B : Type*} [Semiring A] [Semiring B] (φ : A →+* B)
    {I M N : Type*} [AddCommMonoid M] [AddCommMonoid N] [Module A M] [Module B N]
    (F : (I →₀ M) →+ N) (hF : ∀ (i : I) (a : A) (m : M),
      F (.single i (a • m)) = φ a • F (.single i m))
    (a : A) (x : I →₀ M) : F (a • x) = φ a • F x := by
  induction x using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp [smul_add, hx, hy]
  | single i m => simpa [Finsupp.smul_single] using hF i a m

/-- `freeMap` is semilinear for a ring map along which the coefficient map is semilinear. -/
lemma freeMap_smul {A B : Type*} [Semiring A] [Semiring B] (φ : A →+* B)
    {I K M N : Type*} [AddCommMonoid M] [AddCommMonoid N] [Module A M] [Module B N]
    (g : I → K) (ψ : M →+ N) (hψ : ∀ (a : A) (m : M), ψ (a • m) = φ a • ψ m)
    (a : A) (x : I →₀ M) :
    freeMap g ψ (a • x) = φ a • freeMap g ψ x :=
  finsupp_addMonoidHom_smul φ _ (by simp [hψ]) a x

end FreeMap

section LocallySmall

variable {C : Type u} [Category.{w} C] [UnivLE.{u, v}] [UnivLE.{w, v}]

/-- Abelian presheaves with sections in `v` are locally `v`-small when the site is. -/
instance locallySmall_presheaf : LocallySmall.{v} (Cᵒᵖ ⥤ AddCommGrpCat.{v}) where
  hom_small _ _ := small_of_injective (f := fun t ↦ t.app) (fun _ _ h ↦ NatTrans.ext h)

variable (Rp : Cᵒᵖ ⥤ RingCat.{r}) [UnivLE.{r, v}]

/-- Presheaves of modules with sections in `v` are locally `v`-small when the site is. -/
instance locallySmall_presheafOfModules : LocallySmall.{v} (PresheafOfModules.{v} Rp) :=
  locallySmall_of_faithful.{v} (PresheafOfModules.toPresheaf Rp)

variable {J : GrothendieckTopology C} (R : Sheaf J RingCat.{r})

/-- Sheaves of modules with sections in `v` are locally `v`-small when the site is. -/
instance locallySmall_sheafOfModules : LocallySmall.{v} (SheafOfModules.{v} R) :=
  locallySmall_of_faithful.{v} (SheafOfModules.forget R)

end LocallySmall


section Generator

variable {C : Type u} [Category.{w} C] (Rp : Cᵒᵖ ⥤ RingCat.{r})
  [UnivLE.{w, v}] [UnivLE.{r, v}]

/-- The morphism of the site named by an index of the shrunken representable. -/
def basisDown {X : C} {Y : Cᵒᵖ} (i : Shrink.{v} (Y.unop ⟶ X)) : Y.unop ⟶ X :=
  (equivShrink _).symm i

/-- The index of the shrunken representable naming a morphism of the site. -/
def basisUp {X : C} {Y : Cᵒᵖ} (g : Y.unop ⟶ X) : Shrink.{v} (Y.unop ⟶ X) :=
  equivShrink _ g

omit [UnivLE.{r, v}] in
/-- `basisDown` is a left inverse of `basisUp`. -/
@[simp]
lemma basisDown_basisUp {X : C} {Y : Cᵒᵖ} (g : Y.unop ⟶ X) :
    basisDown.{u, v, w} (basisUp.{u, v, w} g) = g :=
  (equivShrink _).symm_apply_apply g

omit [UnivLE.{r, v}] in
/-- `basisDown` is injective. -/
lemma basisDown_injective {X : C} {Y : Cᵒᵖ} :
    Function.Injective (basisDown.{u, v, w} (X := X) (Y := Y)) :=
  (equivShrink _).symm.injective

/-- Restriction on the index set of the free module on a representable. -/
def basisMap {X : C} {Y Z : Cᵒᵖ} (f : Y ⟶ Z) (i : Shrink.{v} (Y.unop ⟶ X)) :
    Shrink.{v} (Z.unop ⟶ X) :=
  basisUp.{u, v, w} (f.unop ≫ basisDown.{u, v, w} i)

omit [UnivLE.{r, v}] in
/-- The morphism named by `basisMap f i` is the composite of `f.unop` with the morphism named
by `i`. -/
@[simp]
lemma basisDown_basisMap {X : C} {Y Z : Cᵒᵖ} (f : Y ⟶ Z)
    (i : Shrink.{v} (Y.unop ⟶ X)) :
    basisDown.{u, v, w} (basisMap.{u, v, w} f i) = f.unop ≫ basisDown.{u, v, w} i :=
  basisDown_basisUp.{u, v, w} _

omit [UnivLE.{r, v}] in
/-- `basisMap` along an identity is the identity. -/
@[simp]
lemma basisMap_id {X : C} {Y : Cᵒᵖ} (i : Shrink.{v} (Y.unop ⟶ X)) :
    basisMap.{u, v, w} (X := X) (𝟙 Y) i = i := by
  simp [basisMap, basisUp, basisDown]

omit [UnivLE.{r, v}] in
/-- `basisMap` along a composite is the composite of the `basisMap`s. -/
@[simp]
lemma basisMap_comp {X : C} {Y Z T : Cᵒᵖ} (f : Y ⟶ Z) (g : Z ⟶ T)
    (i : Shrink.{v} (Y.unop ⟶ X)) :
    basisMap.{u, v, w} (X := X) (f ≫ g) i =
      basisMap.{u, v, w} (X := X) g (basisMap.{u, v, w} (X := X) f i) := by
  simp [basisMap, basisUp, basisDown, Category.assoc]

/-- The shrunken structure ring, as a module over the structure ring. -/
abbrev shrunkRing (Y : Cᵒᵖ) : Type v := Shrink.{v} (Rp.obj Y)

/-- The scalar named by an element of the shrunken structure ring. -/
def coeffDown {Y : Cᵒᵖ} (s : Shrink.{v} (Rp.obj Y)) : Rp.obj Y :=
  Shrink.linearEquiv (Rp.obj Y) (Rp.obj Y) s

/-- The element of the shrunken structure ring naming a scalar. -/
def coeffUp {Y : Cᵒᵖ} (a : Rp.obj Y) : Shrink.{v} (Rp.obj Y) :=
  (Shrink.linearEquiv (Rp.obj Y) (Rp.obj Y)).symm a

omit [UnivLE.{w, v}] in
/-- `coeffDown` is a left inverse of `coeffUp`. -/
@[simp]
lemma coeffDown_coeffUp {Y : Cᵒᵖ} (a : Rp.obj Y) :
    coeffDown.{u, v, w, r} Rp (coeffUp.{u, v, w, r} Rp a) = a :=
  (Shrink.linearEquiv (Rp.obj Y) (Rp.obj Y)).apply_symm_apply a

omit [UnivLE.{w, v}] in
/-- `coeffDown` is injective. -/
lemma coeffDown_injective {Y : Cᵒᵖ} :
    Function.Injective (coeffDown.{u, v, w, r} Rp (Y := Y)) :=
  (Shrink.linearEquiv (Rp.obj Y) (Rp.obj Y)).injective

omit [UnivLE.{w, v}] in
/-- `coeffDown` is additive. -/
@[simp]
lemma coeffDown_add {Y : Cᵒᵖ} (s t : Shrink.{v} (Rp.obj Y)) :
    coeffDown.{u, v, w, r} Rp (s + t) =
      coeffDown.{u, v, w, r} Rp s + coeffDown.{u, v, w, r} Rp t :=
  map_add (Shrink.linearEquiv (Rp.obj Y) (Rp.obj Y)) s t

omit [UnivLE.{w, v}] in
/-- `coeffDown` turns the scalar action into multiplication in the structure ring. -/
@[simp]
lemma coeffDown_smul {Y : Cᵒᵖ} (a : Rp.obj Y) (s : Shrink.{v} (Rp.obj Y)) :
    coeffDown.{u, v, w, r} Rp (a • s) = a * coeffDown.{u, v, w, r} Rp s := by
  rw [← smul_eq_mul]
  exact map_smul (Shrink.linearEquiv (Rp.obj Y) (Rp.obj Y)) a s

/-- Restriction on the coefficients of the free module on a representable, namely the
structure ring shrunk into the module universe. -/
def coeffMap {Y Z : Cᵒᵖ} (f : Y ⟶ Z) :
    Shrink.{v} (Rp.obj Y) →+ Shrink.{v} (Rp.obj Z) :=
  AddMonoidHom.mk'
    (fun s ↦ coeffUp.{u, v, w, r} Rp ((Rp.map f).hom (coeffDown.{u, v, w, r} Rp s)))
    (fun s t ↦ coeffDown_injective.{u, v, w, r} Rp (by
      simp only [coeffDown_coeffUp, coeffDown_add, map_add]))

omit [UnivLE.{w, v}] in
/-- The scalar named by `coeffMap f s` is the restriction along `f` of the scalar named by
`s`. -/
@[simp]
lemma coeffDown_coeffMap {Y Z : Cᵒᵖ} (f : Y ⟶ Z) (s : Shrink.{v} (Rp.obj Y)) :
    coeffDown.{u, v, w, r} Rp (coeffMap.{u, v, w, r} Rp f s) =
      (Rp.map f).hom (coeffDown.{u, v, w, r} Rp s) :=
  coeffDown_coeffUp.{u, v, w, r} Rp _

omit [UnivLE.{w, v}] in
/-- `coeffMap` along an identity is the identity. -/
@[simp]
lemma coeffMap_id {Y : Cᵒᵖ} (s : Shrink.{v} (Rp.obj Y)) :
    coeffMap.{u, v, w, r} Rp (𝟙 Y) s = s :=
  coeffDown_injective.{u, v, w, r} Rp (by
    rw [coeffDown_coeffMap, Rp.map_id]
    rfl)

omit [UnivLE.{w, v}] in
/-- `coeffMap` along a composite is the composite of the `coeffMap`s. -/
@[simp]
lemma coeffMap_comp {Y Z T : Cᵒᵖ} (f : Y ⟶ Z) (g : Z ⟶ T)
    (s : Shrink.{v} (Rp.obj Y)) :
    coeffMap.{u, v, w, r} Rp (f ≫ g) s =
      coeffMap.{u, v, w, r} Rp g (coeffMap.{u, v, w, r} Rp f s) :=
  coeffDown_injective.{u, v, w, r} Rp (by
    simp only [coeffDown_coeffMap, Rp.map_comp, RingCat.hom_comp, RingHom.coe_comp,
      Function.comp_apply])

omit [UnivLE.{w, v}] in
/-- `coeffMap f` is semilinear along the restriction map `Rp.map f`. -/
lemma coeffMap_smul {Y Z : Cᵒᵖ} (f : Y ⟶ Z) (a : Rp.obj Y)
    (s : Shrink.{v} (Rp.obj Y)) :
    coeffMap.{u, v, w, r} Rp f (a • s) =
      (Rp.map f).hom a • coeffMap.{u, v, w, r} Rp f s :=
  coeffDown_injective.{u, v, w, r} Rp (by
    simp only [coeffDown_coeffMap, coeffDown_smul, map_mul])

/-- The underlying abelian presheaf of the free module on the representable at `X`. -/
def generatorPresheaf (X : C) : Cᵒᵖ ⥤ AddCommGrpCat.{v} where
  obj Y := AddCommGrpCat.of (Shrink.{v} (Y.unop ⟶ X) →₀ Shrink.{v} (Rp.obj Y))
  map f := AddCommGrpCat.ofHom
    (freeMap (basisMap.{u, v, w} (X := X) f) (coeffMap.{u, v, w, r} Rp f))
  map_id Y := by
    apply AddCommGrpCat.hom_ext
    apply Finsupp.addHom_ext
    intro i a
    simp
  map_comp f g := by
    apply AddCommGrpCat.hom_ext
    apply Finsupp.addHom_ext
    intro i a
    simp

/-- The sections of `generatorPresheaf` over `Y` form a module over the structure ring at
`Y`. -/
instance generatorModule (X : C) (Y : Cᵒᵖ) :
    Module (Rp.obj Y) ((generatorPresheaf.{u, v, w, r} Rp X).obj Y) :=
  inferInstanceAs
    (Module (Rp.obj Y) (Shrink.{v} (Y.unop ⟶ X) →₀ Shrink.{v} (Rp.obj Y)))

/-- The free module on the representable at `X`, as a presheaf of modules with sections in
the module universe. -/
def generator (X : C) : PresheafOfModules.{v} Rp :=
  PresheafOfModules.ofPresheaf (generatorPresheaf.{u, v, w, r} Rp X)
    (fun {_ _} f a m ↦ freeMap_smul (Rp.map f).hom _ _
      (coeffMap_smul.{u, v, w, r} Rp f) a m)

/-- The additive map underlying `generatorDesc`: the basis element indexed by `i` is sent to
the restriction of the chosen section along `i`. -/
def generatorDescApp {X : C} (M : PresheafOfModules.{v} Rp) (m : M.obj (op X))
    (Y : Cᵒᵖ) :
    (Shrink.{v} (Y.unop ⟶ X) →₀ Shrink.{v} (Rp.obj Y)) →+ M.obj Y :=
  Finsupp.liftAddHom (fun i ↦ AddMonoidHom.mk'
    (fun s ↦ coeffDown.{u, v, w, r} Rp s •
      M.restrictₛₗ (basisDown.{u, v, w} i).op m)
    (fun a b ↦ by rw [coeffDown_add, add_smul]))

/-- `generatorDescApp` sends `Finsupp.single i s` to the scalar named by `s` times the
restriction of `m` along the morphism named by `i`. -/
@[simp]
lemma generatorDescApp_single {X : C} (M : PresheafOfModules.{v} Rp) (m : M.obj (op X))
    (Y : Cᵒᵖ) (i : Shrink.{v} (Y.unop ⟶ X)) (s : Shrink.{v} (Rp.obj Y)) :
    generatorDescApp.{u, v, w, r} Rp M m Y (Finsupp.single i s) =
      coeffDown.{u, v, w, r} Rp s • M.restrictₛₗ (basisDown.{u, v, w} i).op m := by
  rw [generatorDescApp, Finsupp.liftAddHom_apply_single, AddMonoidHom.mk'_apply]

/-- `generatorDescApp` is linear over the structure ring. -/
lemma generatorDescApp_smul {X : C} (M : PresheafOfModules.{v} Rp) (m : M.obj (op X))
    (Y : Cᵒᵖ) (a : Rp.obj Y)
    (x : Shrink.{v} (Y.unop ⟶ X) →₀ Shrink.{v} (Rp.obj Y)) :
    generatorDescApp.{u, v, w, r} Rp M m Y (a • x) =
      a • generatorDescApp.{u, v, w, r} Rp M m Y x :=
  finsupp_addMonoidHom_smul (RingHom.id _) _
    (fun i a s ↦ by
      rw [generatorDescApp_single, generatorDescApp_single, RingHom.id_apply, smul_smul]
      exact congrArg (· • M.restrictₛₗ (basisDown.{u, v, w} i).op m)
        (coeffDown_smul.{u, v, w, r} Rp a s)) a x

/-- The morphism out of the free module on the representable at `X` determined by a section
over `X`. -/
def generatorDesc {X : C} (M : PresheafOfModules.{v} Rp) (m : M.obj (op X)) :
    generator.{u, v, w, r} Rp X ⟶ M :=
  PresheafOfModules.homMk
    { app Y := AddCommGrpCat.ofHom (generatorDescApp.{u, v, w, r} Rp M m Y)
      naturality := by
        intro Y Z f
        apply AddCommGrpCat.hom_ext
        apply Finsupp.addHom_ext
        intro i a
        change generatorDescApp.{u, v, w, r} Rp M m Z
            (freeMap (basisMap.{u, v, w} (X := X) f) (coeffMap.{u, v, w, r} Rp f)
              (Finsupp.single i a)) =
          M.map f (generatorDescApp.{u, v, w, r} Rp M m Y (Finsupp.single i a))
        have hb : basisDown.{u, v, w} (basisMap.{u, v, w} (X := X) f i) =
            f.unop ≫ basisDown.{u, v, w} i := basisDown_basisMap.{u, v, w} f i
        rw [freeMap_single, generatorDescApp_single, generatorDescApp_single,
          PresheafOfModules.map_smul, PresheafOfModules.restrictₛₗ_apply,
          PresheafOfModules.restrictₛₗ_apply, coeffDown_coeffMap, hb,
          CategoryTheory.op_comp, Quiver.Hom.op_unop, PresheafOfModules.map_comp_apply]
        rfl }
    (fun Y a x ↦ generatorDescApp_smul.{u, v, w, r} Rp M m Y a x)

/-- `generatorDesc M m` sends `Finsupp.single i s` to the scalar named by `s` times the
restriction of `m` along the morphism named by `i`. -/
@[simp]
lemma generatorDesc_app_single {X : C} (M : PresheafOfModules.{v} Rp) (m : M.obj (op X))
    (Y : Cᵒᵖ) (i : Shrink.{v} (Y.unop ⟶ X)) (s : Shrink.{v} (Rp.obj Y)) :
    (generatorDesc.{u, v, w, r} Rp M m).app Y (Finsupp.single i s) =
      coeffDown.{u, v, w, r} Rp s • M.restrictₛₗ (basisDown.{u, v, w} i).op m :=
  generatorDescApp_single.{u, v, w, r} Rp M m Y i s

/-- The canonical section of `generator` over `X`, the basis element at the identity. -/
def generatorUnit (X : C) : (generator.{u, v, w, r} Rp X).obj (op X) :=
  Finsupp.single (basisUp.{u, v, w} (𝟙 X)) (coeffUp.{u, v, w, r} Rp 1)

/-- `generatorDesc M m` sends `generatorUnit` to `m`. -/
lemma generatorDesc_app_generatorUnit {X : C} (M : PresheafOfModules.{v} Rp)
    (m : M.obj (op X)) :
    (generatorDesc.{u, v, w, r} Rp M m).app (op X)
      (generatorUnit.{u, v, w, r} Rp X) = m := by
  have hb : basisDown.{u, v, w} (basisUp.{u, v, w} (𝟙 X)) = 𝟙 X :=
    basisDown_basisUp.{u, v, w} (𝟙 X)
  rw [generatorUnit, generatorDesc_app_single, coeffDown_coeffUp,
    PresheafOfModules.restrictₛₗ_apply, hb]
  simp

/-- The composite of `generatorDesc M m` with `φ : M ⟶ N` sends `generatorUnit` to
`φ.app (op X) m`. -/
lemma generatorDesc_comp_app_generatorUnit {X : C} {M N : PresheafOfModules.{v} Rp}
    (m : M.obj (op X)) (φ : M ⟶ N) :
    (generatorDesc.{u, v, w, r} Rp M m ≫ φ).app (op X)
      (generatorUnit.{u, v, w, r} Rp X) = φ.app (op X) m := by
  have h : (generatorDesc.{u, v, w, r} Rp M m ≫ φ).app (op X)
        (generatorUnit.{u, v, w, r} Rp X) =
      φ.app (op X) ((generatorDesc.{u, v, w, r} Rp M m).app (op X)
        (generatorUnit.{u, v, w, r} Rp X)) := rfl
  rw [h, generatorDesc_app_generatorUnit]

end Generator

section Separator

variable {C : Type u} [Category.{w} C] (Rp : Cᵒᵖ ⥤ RingCat.{r})
  [UnivLE.{u, v}] [UnivLE.{w, v}] [UnivLE.{r, v}]

/-- The family of free modules on the shrunken representables, indexed by a `v`-small copy
of the objects of the site so that its coproduct exists. -/
def generators : ObjectProperty (PresheafOfModules.{v} Rp) :=
  .ofObj (fun X : Shrink.{v} C ↦ generator.{u, v, w, r} Rp ((equivShrink C).symm X))

/-- The free modules on the shrunken representables form a separating family of presheaves
of modules. -/
theorem generators_isSeparating : (generators.{u, v, w, r} Rp).IsSeparating := by
  intro M N f g h
  apply PresheafOfModules.hom_ext
  intro X
  ext m
  have hX : (equivShrink C).symm (equivShrink C X.unop) = X.unop :=
    (equivShrink C).symm_apply_apply X.unop
  have key := h _ ⟨equivShrink C X.unop⟩
  rw [hX] at key
  have hφ := fun φ : M ⟶ N ↦ generatorDesc_comp_app_generatorUnit.{u, v, w, r} Rp
    (X := X.unop) (op_unop X ▸ m) φ
  rw [← hφ f, ← hφ g, key (generatorDesc.{u, v, w, r} Rp M (op_unop X ▸ m))]

/-- Presheaves of modules with sections in `v` have a separator when the site and the rings
are `v`-small. -/
instance hasSeparator_presheafOfModules : HasSeparator (PresheafOfModules.{v} Rp) :=
  ⟨_, (generators_isSeparating.{u, v, w, r} Rp).isSeparator_coproduct⟩

/-- Presheaves of modules with sections in `v` form a Grothendieck abelian category when the
site and the rings are `v`-small. -/
instance isGrothendieckAbelian_presheafOfModules :
    IsGrothendieckAbelian.{v} (PresheafOfModules.{v} Rp) where
  hasFilteredColimitsOfSize := ⟨fun _ ↦ ⟨fun _ ↦ inferInstance⟩⟩
  ab5OfSize := ⟨fun D _ _ ↦ ⟨⟨fun K _ _ ↦ ⟨fun {F} ↦
    have : PreservesLimit F (colim (J := D) ⋙ PresheafOfModules.toPresheaf Rp) :=
      preservesLimit_of_natIso _
        (preservesColimitNatIso (PresheafOfModules.toPresheaf Rp)).symm
    preservesLimit_of_reflects_of_preserves _ (PresheafOfModules.toPresheaf Rp)⟩⟩⟩⟩

end Separator

section Sheaf

variable {C : Type u} [Category.{w} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{r}) [HasSheafify J AddCommGrpCat.{v}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{v}]
  [UnivLE.{u, v}] [UnivLE.{w, v}] [UnivLE.{r, v}]

/-- Sheaves of modules with sections in `v` form a Grothendieck abelian category when the
site and the rings are `v`-small. -/
instance isGrothendieckAbelian_sheafOfModules :
    IsGrothendieckAbelian.{v} (SheafOfModules.{v} R) where
  hasFilteredColimitsOfSize := ⟨fun _ ↦ ⟨fun _ ↦ inferInstance⟩⟩
  ab5OfSize := ⟨fun K _ _ ↦
    (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).hasExactColimitsOfShape K⟩
  hasSeparator :=
    .of_adjunction (PresheafOfModules.sheafificationAdjunction (𝟙 R.obj))

end Sheaf

end Stacks.SheafOfModules.Small

end
