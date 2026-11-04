module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedBimoduleTensorAction

/-!
# The presheaf of slice families of a presheaf of modules

Let `R` be a presheaf of rings on a site `C`, let `L` be a presheaf of `R`-modules and let
`U : C`. This file builds the presheaf of modules `Stacks.sliceFamily L U` whose sections over
`W` are the families of sections `z_{X, k, g} ∈ L(X)` indexed by a pair of morphisms
`k : X ⟶ W` and `g : X ⟶ U` and compatible with restriction. It is the right Kan extension
along `Over.forget U` of the restriction of `L` to the slice category over `U`: a morphism of
presheaves of modules `P ⟶ sliceFamily L U` on `C` is the same datum as a morphism
`P|_U ⟶ L|_U` on the slice category.

This is what lets a construction whose universal property produces only *global* morphisms —
such as the relative tensor product, whose sections cannot be written down — be used to produce
a morphism over a slice site.

## Main definitions

* `Stacks.sliceFamily` is the presheaf of slice families, with `Stacks.zApp` the component of a
  section at a pair of morphisms and `Stacks.zMk` a section built from a compatible family.
* `Stacks.sliceFamilyBil` pushes a bilinear map `L × G ⟶ L'` forward to a bilinear map
  `sliceFamily L U × G ⟶ sliceFamily L' U`, componentwise.

## Main results

* `Stacks.zApp_ext`: a section of `sliceFamily L U` is determined by its components.
* `Stacks.zApp_naturality`: the components of a section are compatible with restriction; this
  is the defining condition.
* `Stacks.zApp_sliceFamilyBil` computes the components of `sliceFamilyBil`.

## Implementation notes

The plumbing is the same shape as `Stacks.bilinHom` in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/GradedBimoduleTensorAction.lean`, whose sections
over `W` are the families of maps on sections indexed by the morphisms out of `W`: the sections
are a submodule of a product indexed by morphisms of the site, the scalars act through the
restriction map of the index, and the API is a component map `zApp`, a constructor `zMk` and an
extensionality principle `zApp_ext`.

Unlike `Stacks.bilinHom`, no commutativity of the base is needed: the defining condition on a
family mentions no second variable, so the two scalars never have to be commuted.

Sections over `W` are indexed by morphisms of the site, so the presheaf lives in the join of the
module universe with the universes of the site. The module universe `m` must therefore satisfy
`m = max u v z m` as a level, and the general solution of that is `max u v z z` with `z` free:
every universe at least as large as the site's, which is what the module universe is written at
here. The universe `t` of the presheaf of rings is unrelated to it.

## References

* [Stacks Project, Tag 00XB](https://stacks.math.columbia.edu/tag/00XB) — the localized site
  `C/U`.
-/

@[expose] public section

open CategoryTheory

universe t v u z

namespace Stacks

variable {C : Type u} [Category.{v} C] {R : Cᵒᵖ ⥤ RingCat.{t}}

/-- Families of sections `z_{X, k, g} ∈ L(X)` indexed by a pair of morphisms `k : X ⟶ W` of the
site and `g : X ⟶ U`. -/
abbrev SliceFamilyPi (L : PresheafOfModules.{max u v z} R) (U : C) (W : Cᵒᵖ) :
    Type (max u v z) :=
  ∀ (X : Cᵒᵖ), (W ⟶ X) → (X.unop ⟶ U) → L.obj X

variable {L L' : PresheafOfModules.{max u v z} R} {U : C}

/-- The families `SliceFamilyPi L U W` form an `R(W)`-module, a scalar `r` acting on the
component at `k : X ⟶ W` through its restriction along `k`. -/
instance (W : Cᵒᵖ) : Module (R.obj W) (SliceFamilyPi L U W) where
  smul r z := fun X k g => R.map k r • z X k g
  one_smul z := by
    funext X k g
    change R.map k (1 : _) • z X k g = z X k g
    simp
  mul_smul r s z := by
    funext X k g
    change R.map k (r * s) • z X k g = R.map k r • R.map k s • z X k g
    rw [map_mul, mul_smul]
  smul_zero r := by
    funext X k g
    change R.map k r • (0 : L.obj X) = 0
    rw [smul_zero]
  smul_add r z z' := by
    funext X k g
    change R.map k r • (z X k g + z' X k g) = R.map k r • z X k g + R.map k r • z' X k g
    rw [smul_add]
  add_smul r s z := by
    funext X k g
    change R.map k (r + s) • z X k g = R.map k r • z X k g + R.map k s • z X k g
    rw [map_add, add_smul]
  zero_smul z := by
    funext X k g
    change R.map k (0 : _) • z X k g = 0
    simp

/-- The sections over `W` of the presheaf of slice families: the families compatible with
restriction. -/
def sliceFamilySubmodule (L : PresheafOfModules.{max u v z} R) (U : C) (W : Cᵒᵖ) :
    Submodule (R.obj W) (SliceFamilyPi L U W) where
  carrier := {z | ∀ (X Y : Cᵒᵖ) (k : W ⟶ X) (g : X.unop ⟶ U) (h : X ⟶ Y),
    restr L h (z X k g) = z Y (k ≫ h) (h.unop ≫ g)}
  zero_mem' X Y k g h := by
    change L.map h (0 : L.obj X) = (0 : L.obj Y)
    rw [map_zero]
    rfl
  add_mem' {z z'} hz hz' X Y k g h := by
    change restr L h (z X k g + z' X k g) = z Y (k ≫ h) _ + z' Y (k ≫ h) _
    rw [restr_add, hz X Y k g h, hz' X Y k g h]
  smul_mem' r z hz X Y k g h := by
    change restr L h (R.map k r • z X k g) = R.map (k ≫ h) r • z Y (k ≫ h) (h.unop ≫ g)
    rw [restr_smul, hz X Y k g h]
    congr 1
    simp

/-- **The presheaf of slice families of `L` over `U`**: its sections over `W` are the families
of sections `z_{X, k, g} ∈ L(X)`, indexed by a pair of morphisms `k : X ⟶ W` and `g : X ⟶ U`,
which are compatible with restriction. -/
noncomputable def sliceFamily (L : PresheafOfModules.{max u v z} R) (U : C) :
    PresheafOfModules.{max u v z} R where
  obj W := ModuleCat.of _ (sliceFamilySubmodule L U W)
  map {W W'} f := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (R.map f).hom).obj
      (ModuleCat.of _ (sliceFamilySubmodule L U W')))
    { toFun := fun z => ⟨fun X k g => z.1 X (f ≫ k) g, fun X Y k g h => by
        rw [z.2 X Y (f ≫ k) g h, Category.assoc]⟩
      map_add' := fun z z' => rfl
      map_smul' := fun r z => by
        refine Subtype.ext ?_
        funext X k g
        change R.map (f ≫ k) r • z.1 X (f ≫ k) g = R.map k (R.map f r) • z.1 X (f ≫ k) g
        congr 1
        simp }
  map_id W := by
    refine ModuleCat.hom_ext (LinearMap.ext fun z => Subtype.ext ?_)
    funext X k g
    change z.1 X (𝟙 W ≫ k) g = z.1 X k g
    rw [Category.id_comp]
  map_comp {W W' W''} f f' := by
    refine ModuleCat.hom_ext (LinearMap.ext fun z => Subtype.ext ?_)
    funext X k g
    change z.1 X ((f ≫ f') ≫ k) g = z.1 X (f ≫ f' ≫ k) g
    rw [Category.assoc]

/-- The component of a slice family at a pair of morphisms. -/
def zApp {W : Cᵒᵖ} (z : (sliceFamily L U).obj W) {X : Cᵒᵖ} (k : W ⟶ X) (g : X.unop ⟶ U) :
    L.obj X :=
  z.1 X k g

/-- A slice family, from a compatible family of sections. -/
def zMk {W : Cᵒᵖ} (z : ∀ (X : Cᵒᵖ), (W ⟶ X) → (X.unop ⟶ U) → L.obj X)
    (hnat : ∀ (X Y : Cᵒᵖ) (k : W ⟶ X) (g : X.unop ⟶ U) (h : X ⟶ Y),
      restr L h (z X k g) = z Y (k ≫ h) (h.unop ≫ g)) :
    (sliceFamily L U).obj W :=
  ⟨z, hnat⟩

/-- The components of `zMk z hnat` are the sections of the family `z`. -/
@[simp]
theorem zApp_zMk {W : Cᵒᵖ} (z) (hnat) {X : Cᵒᵖ} (k : W ⟶ X) (g : X.unop ⟶ U) :
    zApp (L := L) (zMk z hnat) k g = z X k g := rfl

/-- The components of a slice family are compatible with restriction. -/
theorem zApp_naturality {W : Cᵒᵖ} (z : (sliceFamily L U).obj W) {X Y : Cᵒᵖ} (k : W ⟶ X)
    (g : X.unop ⟶ U) (h : X ⟶ Y) : restr L h (zApp z k g) = zApp z (k ≫ h) (h.unop ≫ g) :=
  z.2 X Y k g h

/-- Two slice families with the same components are equal. -/
theorem zApp_ext {W : Cᵒᵖ} {z z' : (sliceFamily L U).obj W}
    (h : ∀ (X : Cᵒᵖ) (k : W ⟶ X) (g : X.unop ⟶ U), zApp z k g = zApp z' k g) : z = z' := by
  refine Subtype.ext ?_
  funext X k g
  exact h X k g

/-- The components of the zero slice family are zero. -/
@[simp]
theorem zApp_zero {W X : Cᵒᵖ} (k : W ⟶ X) (g : X.unop ⟶ U) :
    zApp (L := L) (U := U) (0 : (sliceFamily L U).obj W) k g = 0 := rfl

/-- The components of a sum of slice families are the sums of the components. -/
@[simp]
theorem zApp_add {W : Cᵒᵖ} (z z' : (sliceFamily L U).obj W) {X : Cᵒᵖ} (k : W ⟶ X)
    (g : X.unop ⟶ U) : zApp (z + z') k g = zApp z k g + zApp z' k g := rfl

/-- The component at `k` of `r • z` is the component of `z` multiplied by the restriction of `r`
along `k`. -/
@[simp]
theorem zApp_smul {W : Cᵒᵖ} (r : R.obj W) (z : (sliceFamily L U).obj W) {X : Cᵒᵖ} (k : W ⟶ X)
    (g : X.unop ⟶ U) : zApp (r • z) k g = R.map k r • zApp z k g := rfl

/-- The component at `k` of the restriction of a slice family along `f` is its component at
`f ≫ k`. -/
@[simp]
theorem zApp_restr {W W' : Cᵒᵖ} (f : W ⟶ W') (z : (sliceFamily L U).obj W) {X : Cᵒᵖ}
    (k : W' ⟶ X) (g : X.unop ⟶ U) :
    zApp (restr (sliceFamily L U) f z) k g = zApp z (f ≫ k) g := rfl

/-- A slice family is linear over the base in the component at the identity. -/
theorem zApp_id_smul {W : Cᵒᵖ} (r : R.obj W) (z : (sliceFamily L U).obj W) (g : W.unop ⟶ U) :
    zApp (r • z) (𝟙 W) g = r • zApp z (𝟙 W) g := by
  rw [zApp_smul]
  congr 1
  simp

variable {G : PresheafOfModules.{max u v z} R}

/-- A bilinear map `L × G ⟶ L'` applied componentwise to slice families, the second variable
being restricted along the index. -/
noncomputable def sliceFamilyBil (μ : BilinearMap L G L') (U : C) :
    BilinearMap (sliceFamily L U) G (sliceFamily L' U) where
  app W := AddMonoidHom.mk'
    (fun z => AddMonoidHom.mk'
      (fun b => zMk (fun X k g => μ.app X (zApp z k g) (restr G k b))
        (fun X Y k g h => by
          rw [μ.restr_bil h, zApp_naturality, restr_restr]))
      (fun b b' => zApp_ext fun X k g => by
        change μ.app X (zApp z k g) (restr G k (b + b')) =
          μ.app X (zApp z k g) (restr G k b) + μ.app X (zApp z k g) (restr G k b')
        rw [restr_add, map_add]))
    (fun z z' => AddMonoidHom.ext fun b => zApp_ext fun X k g => by
      change μ.app X (zApp (z + z') k g) (restr G k b) =
        μ.app X (zApp z k g) (restr G k b) + μ.app X (zApp z' k g) (restr G k b)
      rw [zApp_add, μ.map_add_left])
  map_smul_left W r z b := zApp_ext fun X k g => by
    change μ.app X (zApp (r • z) k g) (restr G k b) =
      R.map k r • μ.app X (zApp z k g) (restr G k b)
    rw [zApp_smul, μ.map_smul_left]
  map_smul_right W r z b := zApp_ext fun X k g => by
    change μ.app X (zApp z k g) (restr G k (r • b)) =
      R.map k r • μ.app X (zApp z k g) (restr G k b)
    rw [restr_smul, μ.map_smul_right]
  naturality {W W'} f z b := zApp_ext fun X k g => by
    change μ.app X (zApp z (f ≫ k) g) (restr G (f ≫ k) b) =
      μ.app X (zApp (restr (sliceFamily L U) f z) k g) (restr G k (restr G f b))
    rw [zApp_restr, restr_restr]

/-- The component at `k` of `sliceFamilyBil μ U` applied to `z` and `b` is `μ` applied to the
component of `z` at `k` and the restriction of `b` along `k`. -/
@[simp]
theorem zApp_sliceFamilyBil (μ : BilinearMap L G L') (U : C) {W : Cᵒᵖ}
    (z : (sliceFamily L U).obj W) (b : G.obj W) {X : Cᵒᵖ} (k : W ⟶ X) (g : X.unop ⟶ U) :
    zApp ((sliceFamilyBil μ U).app W z b) k g = μ.app X (zApp z k g) (restr G k b) := rfl

/-- The component at the identity of a componentwise bilinear map is the bilinear map. -/
theorem zApp_id_sliceFamilyBil (μ : BilinearMap L G L') (U : C) {W : Cᵒᵖ}
    (z : (sliceFamily L U).obj W) (b : G.obj W) (g : W.unop ⟶ U) :
    zApp ((sliceFamilyBil μ U).app W z b) (𝟙 W) g = μ.app W (zApp z (𝟙 W) g) b := by
  rw [zApp_sliceFamilyBil, restr_id]

end Stacks

end
