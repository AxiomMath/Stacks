module

public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.EssentiallySmall
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Types.Limits
public import Mathlib.CategoryTheory.Yoneda
public import Mathlib.Logic.Small.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The dependent product (Weil restriction) of presheaves along a morphism

Let `C` be a category and let `f : V ⟶ W` be a morphism of presheaves of types on `C`. Base
change along `f` is the functor `CategoryTheory.Over.pullback f : Over W ⥤ Over V`. This file
constructs the object part of its right adjoint

  `CategoryTheory.Presheaf.depProd f : Over V ⥤ Over W`,

the *dependent product*, or *Weil restriction*, along `f`.

Classically the dependent product of `Y ⟶ V` along `f : V ⟶ W` is the presheaf whose sections
over `A` are the pairs `(w, y)` where `w : A ⟶ W` and `y : A ×_{w, W} V ⟶ Y` is a morphism over
`V`. Rather than form that fibre product, we record such a `y` by the *family of its values*: a
morphism `A ×_{w, W} V ⟶ Y` over `V` is exactly a rule assigning, to each `h : A' ⟶ A` and each
section `v` of `V` over `A'` whose image in `W` is `h^* w`, a section of `Y` over `A'` lying over
`v`, naturally in `A'`. That family is `DepProdSectionRaw`, and the dependent product presheaf
`depProdObj f Y` has `Σ w, DepProdSection f Y A w` as its sections over `A`.

## Main definitions

* `CategoryTheory.Presheaf.pullbackElt`: an element of a pullback of presheaves, from a
  compatible pair.
* `CategoryTheory.Presheaf.DepProdSectionRaw`: the family-of-values description, before shrinking.
* `CategoryTheory.Presheaf.DepProdSection`: the same, shrunk into `Type v₁`.
* `CategoryTheory.Presheaf.depProdObj`: the dependent product as a presheaf.
* `CategoryTheory.Presheaf.depProdπ`: its structure morphism to `W`, which reads off `w`.
* `CategoryTheory.Presheaf.depProd`: the dependent product as a functor `Over V ⥤ Over W`.
* `CategoryTheory.Presheaf.depProdCounitApp`: the evaluation map
  `(Over.pullback f).obj ((depProd f).obj Y) ⟶ Y`, the counit of the adjunction.

## Implementation notes

The construction assumes `[LocallySmall.{v₁} (Cᵒᵖ ⥤ Type v₁)]`, and the category `C` is not
assumed small: objects live in `Type u₁` and presheaves are valued in `Type v₁`.

`DepProdSectionRaw f Y A w` is a `Π` over the objects and the arrows of `C`, so it lands in
`Type (max u₁ v₁)`, one universe too high to be the sections of a presheaf of `Type v₁`. A raw
section is determined by the morphism `A ×_{w, W} V ⟶ Y` it names (`DepProdSectionRaw.toHom`,
injective by evaluation at `pullbackElt`), and homs of presheaves are `v₁`-small by
`LocallySmall`, so raw sections are `v₁`-small, and the sections used are
`DepProdSection f Y A w := Shrink.{v₁} (DepProdSectionRaw f Y A w)`. Only the second component
of the pair is shrunk. The accessors `DepProdSection.app`, `DepProdSection.over`,
`DepProdSection.naturality`, `DepProdSection.restrict`, `DepProdSection.ext_app`,
`DepProdSection.app_congr` and the constructor `DepProdSection.mk'` describe a section by its
family of values.
-/

@[expose] public section

open CategoryTheory Opposite

namespace CategoryTheory.Presheaf

universe v₁ u₁

variable {C : Type u₁} [Category.{v₁} C] {V W : Cᵒᵖ ⥤ Type v₁} (f : V ⟶ W)

/-- Elementwise form of an equality of morphisms of presheaves of types. -/
theorem hom_congr_apply {F G : Cᵒᵖ ⥤ Type v₁} {α β : F ⟶ G} (h : α = β) (A : Cᵒᵖ)
    (x : F.obj A) : α.app A x = β.app A x :=
  types_congr_hom (NatTrans.congr_app h A) x

/-- A section `v` of `V` over `A'` lying over `h^* g^* w` lies over `(h ≫ g)^* w`. -/
theorem comp_compat {A A₀ : C} (g : A₀ ⟶ A) {w : W.obj (op A)} {A' : C} (h : A' ⟶ A₀)
    {v : V.obj (op A')} (hv : f.app (op A') v = W.map h.op (W.map g.op w)) :
    f.app (op A') v = W.map (h ≫ g).op w := by
  simpa only [op_comp, Functor.map_comp_apply] using hv

/-- Restricting a section `v` of `V` along `k` keeps it lying over the correspondingly
restricted section of `W`. -/
theorem map_compat {A : C} {w : W.obj (op A)} {A₁ A₂ : C} (k : A₂ ⟶ A₁) (h : A₁ ⟶ A)
    {v : V.obj (op A₁)} (hv : f.app (op A₁) v = W.map h.op w) :
    f.app (op A₂) (V.map k.op v) = W.map (k ≫ h).op w := by
  rw [NatTrans.naturality_apply, hv, op_comp, Functor.map_comp_apply]

/-! ### Elements of a pullback of presheaves -/

section PullbackElt

variable {F G H : Cᵒᵖ ⥤ Type v₁} (a : F ⟶ H) (b : G ⟶ H)

/-- An element of the pullback of two morphisms of presheaves, built from a compatible pair of
elements. Pullbacks of presheaves are computed pointwise, and this is that pointwise pair,
transported through the Yoneda lemma so that no concrete model of the pullback is needed. -/
noncomputable def pullbackElt {A : C} (x : F.obj (op A)) (y : G.obj (op A))
    (hxy : a.app (op A) x = b.app (op A) y) : (Limits.pullback a b).obj (op A) :=
  yonedaEquiv (Limits.pullback.lift (yonedaEquiv.symm x) (yonedaEquiv.symm y) (by
    rw [yonedaEquiv_symm_naturality_right, yonedaEquiv_symm_naturality_right, hxy]))

/-- An element of a pullback of presheaves is determined by its two projections. -/
theorem pullbackElt_ext {A : C} {e₁ e₂ : (Limits.pullback a b).obj (op A)}
    (h₁ : (Limits.pullback.fst a b).app (op A) e₁ = (Limits.pullback.fst a b).app (op A) e₂)
    (h₂ : (Limits.pullback.snd a b).app (op A) e₁ = (Limits.pullback.snd a b).app (op A) e₂) :
    e₁ = e₂ := by
  apply yonedaEquiv.symm.injective
  refine Limits.pullback.hom_ext ?_ ?_
  · rw [yonedaEquiv_symm_naturality_right, yonedaEquiv_symm_naturality_right, h₁]
  · rw [yonedaEquiv_symm_naturality_right, yonedaEquiv_symm_naturality_right, h₂]

/-- The first projection of `pullbackElt a b x y hxy` is `x`. -/
@[simp]
theorem pullbackElt_fst {A : C} (x : F.obj (op A)) (y : G.obj (op A))
    (hxy : a.app (op A) x = b.app (op A) y) :
    (Limits.pullback.fst a b).app (op A) (pullbackElt a b x y hxy) = x := by
  simp only [pullbackElt, ← yonedaEquiv_comp, Limits.pullback.lift_fst, Equiv.apply_symm_apply]

/-- The second projection of `pullbackElt a b x y hxy` is `y`. -/
@[simp]
theorem pullbackElt_snd {A : C} (x : F.obj (op A)) (y : G.obj (op A))
    (hxy : a.app (op A) x = b.app (op A) y) :
    (Limits.pullback.snd a b).app (op A) (pullbackElt a b x y hxy) = y := by
  simp only [pullbackElt, ← yonedaEquiv_comp, Limits.pullback.lift_snd, Equiv.apply_symm_apply]

/-- `pullbackElt` depends on the two elements only, not on the compatibility proof. -/
theorem pullbackElt_congr {A : C} {x x' : F.obj (op A)} {y y' : G.obj (op A)}
    (hx : x = x') (hy : y = y')
    (hxy : a.app (op A) x = b.app (op A) y) (hxy' : a.app (op A) x' = b.app (op A) y') :
    pullbackElt a b x y hxy = pullbackElt a b x' y' hxy' := by
  subst hx
  subst hy
  rfl

/-- Every element of a pullback of presheaves is the pair of its two projections. -/
@[simp]
theorem pullbackElt_fst_snd {A : C} (e : (Limits.pullback a b).obj (op A)) :
    pullbackElt a b ((Limits.pullback.fst a b).app (op A) e)
        ((Limits.pullback.snd a b).app (op A) e)
        (hom_congr_apply (Limits.pullback.condition (f := a) (g := b)) (op A) e) = e := by
  refine pullbackElt_ext a b ?_ ?_
  · rw [pullbackElt_fst]
  · rw [pullbackElt_snd]

/-- Restriction acts on `pullbackElt` componentwise. -/
theorem pullbackElt_map {A A' : C} (g : A' ⟶ A) (x : F.obj (op A)) (y : G.obj (op A))
    (hxy : a.app (op A) x = b.app (op A) y) :
    (Limits.pullback a b).map g.op (pullbackElt a b x y hxy) =
      pullbackElt a b (F.map g.op x) (G.map g.op y)
        (by rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hxy]) := by
  refine pullbackElt_ext a b ?_ ?_
  · rw [NatTrans.naturality_apply, pullbackElt_fst, pullbackElt_fst]
  · rw [NatTrans.naturality_apply, pullbackElt_snd, pullbackElt_snd]

end PullbackElt

/-! ### The family of values, before shrinking -/

/-- A section of the dependent product of `Y : Over V` along `f : V ⟶ W`, over an object `A` of
`C` and a section `w` of `W` over `A`, before shrinking.

This is the family-of-values description of a morphism `A ×_{w, W} V ⟶ Y` over `V`: to each
`h : A' ⟶ A` and each section `v` of `V` over `A'` lying over `h^* w` it assigns a section of `Y`
over `A'`, lying over `v` and compatible with restriction. -/
structure DepProdSectionRaw (Y : Over V) (A : C) (w : W.obj (op A)) where
  /-- The value of the section at a point `(h, v)` of the fibre product `A ×_{w, W} V`. -/
  app : ∀ {A' : C} (h : A' ⟶ A) (v : V.obj (op A')),
    f.app (op A') v = W.map h.op w → Y.left.obj (op A')
  /-- The values lie over `V`: the morphism `A ×_{w, W} V ⟶ Y` is a morphism over `V`. -/
  over : ∀ {A' : C} (h : A' ⟶ A) (v : V.obj (op A'))
    (hv : f.app (op A') v = W.map h.op w), Y.hom.app (op A') (app h v hv) = v
  /-- The values are compatible with restriction: naturality of `A ×_{w, W} V ⟶ Y`. -/
  naturality : ∀ {A₁ A₂ : C} (k : A₂ ⟶ A₁) (h : A₁ ⟶ A) (v : V.obj (op A₁))
    (hv : f.app (op A₁) v = W.map h.op w),
    Y.left.map k.op (app h v hv) = app (k ≫ h) (V.map k.op v) (map_compat f k h hv)

variable {f}

/-- Two raw sections agree as soon as all their values agree. -/
@[ext]
theorem DepProdSectionRaw.ext_app {Y : Over V} {A : C} {w : W.obj (op A)}
    {y₁ y₂ : DepProdSectionRaw f Y A w}
    (h : ∀ (A' : C) (g : A' ⟶ A) (v : V.obj (op A'))
      (hv : f.app (op A') v = W.map g.op w), y₁.app g v hv = y₂.app g v hv) :
    y₁ = y₂ := by
  obtain ⟨a₁, o₁, n₁⟩ := y₁
  obtain ⟨a₂, o₂, n₂⟩ := y₂
  obtain rfl : @a₁ = @a₂ := by
    funext A' hh v hv
    exact h A' hh v hv
  rfl

/-- The value of a raw section depends on the morphism `h` only through its value. -/
theorem DepProdSectionRaw.app_congr {Y : Over V} {A : C} {w : W.obj (op A)}
    (y : DepProdSectionRaw f Y A w) {A' : C} {g g' : A' ⟶ A} (hg : g = g')
    (v : V.obj (op A')) (hv : f.app (op A') v = W.map g.op w)
    (hv' : f.app (op A') v = W.map g'.op w) :
    y.app g v hv = y.app g' v hv' := by
  subst hg
  rfl

/-- Restriction of a raw section along `g : A₀ ⟶ A`. It is pure reindexing: the value at `h`
becomes the value at `h ≫ g`. -/
def DepProdSectionRaw.restrict {Y : Over V} {A : C} {w : W.obj (op A)}
    (y : DepProdSectionRaw f Y A w) {A₀ : C} (g : A₀ ⟶ A) :
    DepProdSectionRaw f Y A₀ (W.map g.op w) where
  app := fun h v hv => y.app (h ≫ g) v (comp_compat f g h hv)
  over := fun _ _ _ => y.over _ _ _
  naturality := fun k h v hv =>
    (y.naturality k (h ≫ g) v (comp_compat f g h hv)).trans
      (y.app_congr (Category.assoc k h g).symm _ _ _)

/-- The value of the restriction of `y` along `g` at `h` is the value of `y` at `h ≫ g`. -/
@[simp]
theorem DepProdSectionRaw.restrict_app {Y : Over V} {A : C} {w : W.obj (op A)}
    (y : DepProdSectionRaw f Y A w) {A₀ : C} (g : A₀ ⟶ A) {A' : C} (h : A' ⟶ A₀)
    (v : V.obj (op A')) (hv : f.app (op A') v = W.map h.op (W.map g.op w)) :
    (y.restrict g).app h v hv = y.app (h ≫ g) v (comp_compat f g h hv) :=
  rfl

/-! ### Smallness

A raw section names a morphism `A ×_{w, W} V ⟶ Y`, and is determined by it. Homs of the
presheaf category are `v₁`-small under `LocallySmall`, so raw sections are too, and the
sections of the dependent product can live in the universe of the presheaves. -/

section Small

/-- The value of `yonedaEquiv.symm w` at a morphism is the corresponding restriction of `w`. -/
theorem yonedaEquiv_symm_app_apply {A : C} (w : W.obj (op A)) {B : Cᵒᵖ} (h : B.unop ⟶ A) :
    (yonedaEquiv.symm w).app B h = W.map h.op w := by
  simp

/-- The two projections of an element of `A ×_{w, W} V` are compatible, in the form the family
of values asks for. -/
theorem pullback_yonedaEquiv_compat {A : C} {w : W.obj (op A)} {B : Cᵒᵖ}
    (e : (Limits.pullback (yonedaEquiv.symm w) f).obj B) :
    f.app (op B.unop) ((Limits.pullback.snd (yonedaEquiv.symm w) f).app B e) =
      W.map ((Limits.pullback.fst (yonedaEquiv.symm w) f).app B e).op w := by
  have hc := hom_congr_apply
    (Limits.pullback.condition (f := yonedaEquiv.symm w) (g := f)) B e
  simp only [NatTrans.comp_app, types_comp_apply] at hc
  rw [yonedaEquiv_symm_app_apply] at hc
  exact hc.symm

/-- The value of a raw section depends on the morphism and on the section of `V` only through
their values. -/
theorem DepProdSectionRaw.app_congr₂ {Y : Over V} {A : C} {w : W.obj (op A)}
    (y : DepProdSectionRaw f Y A w) {A' : C} {g g' : A' ⟶ A} (hg : g = g')
    {v v' : V.obj (op A')} (hv₀ : v = v')
    (hv : f.app (op A') v = W.map g.op w) (hv' : f.app (op A') v' = W.map g'.op w) :
    y.app g v hv = y.app g' v' hv' := by
  subst hg
  subst hv₀
  rfl

/-- The morphism `A ×_{w, W} V ⟶ Y` named by a raw section. -/
noncomputable def DepProdSectionRaw.toHom {Y : Over V} {A : C} {w : W.obj (op A)}
    (y : DepProdSectionRaw f Y A w) :
    Limits.pullback (yonedaEquiv.symm w) f ⟶ Y.left where
  app := fun B => ↾(fun e =>
    y.app ((Limits.pullback.fst (yonedaEquiv.symm w) f).app B e)
      ((Limits.pullback.snd (yonedaEquiv.symm w) f).app B e)
      (pullback_yonedaEquiv_compat e))
  naturality := by
    intro B₁ B₂ g
    ext e
    have hfst : (Limits.pullback.fst (yonedaEquiv.symm w) f).app B₂
          ((Limits.pullback (yonedaEquiv.symm w) f).map g e)
        = g.unop ≫ (Limits.pullback.fst (yonedaEquiv.symm w) f).app B₁ e :=
      NatTrans.naturality_apply (Limits.pullback.fst (yonedaEquiv.symm w) f) g e
    have hsnd : (Limits.pullback.snd (yonedaEquiv.symm w) f).app B₂
          ((Limits.pullback (yonedaEquiv.symm w) f).map g e)
        = V.map g ((Limits.pullback.snd (yonedaEquiv.symm w) f).app B₁ e) :=
      NatTrans.naturality_apply (Limits.pullback.snd (yonedaEquiv.symm w) f) g e
    have hn := y.naturality g.unop
      ((Limits.pullback.fst (yonedaEquiv.symm w) f).app B₁ e)
      ((Limits.pullback.snd (yonedaEquiv.symm w) f).app B₁ e)
      (pullback_yonedaEquiv_compat e)
    exact Eq.trans
      (y.app_congr₂ hfst hsnd (pullback_yonedaEquiv_compat _)
        (map_compat f g.unop _ (pullback_yonedaEquiv_compat e)))
      hn.symm

/-- A raw section is determined by the morphism `A ×_{w, W} V ⟶ Y` it names. -/
theorem DepProdSectionRaw.toHom_injective {Y : Over V} {A : C} {w : W.obj (op A)} :
    Function.Injective (DepProdSectionRaw.toHom (f := f) (Y := Y) (A := A) (w := w)) := by
  intro y₁ y₂ hy
  refine DepProdSectionRaw.ext_app fun A' h v hv => ?_
  have hcompat : (yonedaEquiv.symm w).app (op A') h = f.app (op A') v := by
    rw [yonedaEquiv_symm_app_apply]
    exact hv.symm
  have hev := hom_congr_apply hy (op A')
    (pullbackElt (yonedaEquiv.symm w) f h v hcompat)
  simp only [DepProdSectionRaw.toHom] at hev
  refine Eq.trans ?_ (Eq.trans hev ?_)
  · exact y₁.app_congr₂ (pullbackElt_fst (yonedaEquiv.symm w) f h v hcompat).symm
      (pullbackElt_snd (yonedaEquiv.symm w) f h v hcompat).symm _ _
  · exact y₂.app_congr₂ (pullbackElt_fst (yonedaEquiv.symm w) f h v hcompat)
      (pullbackElt_snd (yonedaEquiv.symm w) f h v hcompat) _ _

variable [LocallySmall.{v₁} (Cᵒᵖ ⥤ Type v₁)]

/-- Raw sections form a `v₁`-small type: a raw section is determined by the morphism it names,
and homs of the presheaf category are `v₁`-small. -/
instance small_depProdSectionRaw (Y : Over V) (A : C) (w : W.obj (op A)) :
    Small.{v₁} (DepProdSectionRaw f Y A w) :=
  small_of_injective (DepProdSectionRaw.toHom_injective (f := f) (Y := Y) (A := A) (w := w))

variable (f)

/-- A section of the dependent product: a raw family of values, shrunk into the universe of the
presheaves. -/
noncomputable def DepProdSection (Y : Over V) (A : C) (w : W.obj (op A)) : Type v₁ :=
  Shrink.{v₁} (DepProdSectionRaw f Y A w)

variable {f} {Y : Over V} {A : C} {w : W.obj (op A)}

/-- The raw family of values underlying a section. -/
noncomputable def DepProdSection.raw (y : DepProdSection f Y A w) : DepProdSectionRaw f Y A w :=
  (equivShrink (DepProdSectionRaw f Y A w)).symm y

/-- A raw family of values, as a section. -/
noncomputable def DepProdSection.ofRaw (y : DepProdSectionRaw f Y A w) : DepProdSection f Y A w :=
  equivShrink (DepProdSectionRaw f Y A w) y

/-- The raw family of values of `DepProdSection.ofRaw y` is `y`. -/
@[simp]
theorem DepProdSection.raw_ofRaw (y : DepProdSectionRaw f Y A w) :
    (DepProdSection.ofRaw y).raw = y :=
  (equivShrink (DepProdSectionRaw f Y A w)).symm_apply_apply y

/-- A section is the section built from its raw family of values. -/
@[simp]
theorem DepProdSection.ofRaw_raw (y : DepProdSection f Y A w) :
    DepProdSection.ofRaw y.raw = y :=
  (equivShrink (DepProdSectionRaw f Y A w)).apply_symm_apply y

/-- A section is determined by its raw family of values. -/
theorem DepProdSection.raw_injective :
    Function.Injective (DepProdSection.raw (f := f) (Y := Y) (A := A) (w := w)) :=
  (equivShrink (DepProdSectionRaw f Y A w)).symm.injective

/-- The value of a section at a point `(h, v)` of the fibre product `A ×_{w, W} V`. -/
noncomputable def DepProdSection.app (y : DepProdSection f Y A w) {A' : C} (h : A' ⟶ A)
    (v : V.obj (op A')) (hv : f.app (op A') v = W.map h.op w) : Y.left.obj (op A') :=
  y.raw.app h v hv

/-- The values of a section lie over `V`. -/
theorem DepProdSection.over (y : DepProdSection f Y A w) {A' : C} (h : A' ⟶ A)
    (v : V.obj (op A')) (hv : f.app (op A') v = W.map h.op w) :
    Y.hom.app (op A') (y.app h v hv) = v :=
  y.raw.over h v hv

/-- The values of a section are compatible with restriction. -/
theorem DepProdSection.naturality (y : DepProdSection f Y A w) {A₁ A₂ : C} (k : A₂ ⟶ A₁)
    (h : A₁ ⟶ A) (v : V.obj (op A₁)) (hv : f.app (op A₁) v = W.map h.op w) :
    Y.left.map k.op (y.app h v hv) = y.app (k ≫ h) (V.map k.op v) (map_compat f k h hv) :=
  y.raw.naturality k h v hv

/-- Two sections agree as soon as all their values agree. -/
@[ext]
theorem DepProdSection.ext_app {y₁ y₂ : DepProdSection f Y A w}
    (h : ∀ (A' : C) (g : A' ⟶ A) (v : V.obj (op A'))
      (hv : f.app (op A') v = W.map g.op w), y₁.app g v hv = y₂.app g v hv) :
    y₁ = y₂ :=
  DepProdSection.raw_injective (DepProdSectionRaw.ext_app h)

/-- The value of a section depends on the morphism `h` only through its value. -/
theorem DepProdSection.app_congr (y : DepProdSection f Y A w) {A' : C} {g g' : A' ⟶ A}
    (hg : g = g') (v : V.obj (op A')) (hv : f.app (op A') v = W.map g.op w)
    (hv' : f.app (op A') v = W.map g'.op w) :
    y.app g v hv = y.app g' v hv' :=
  y.raw.app_congr hg v hv hv'

/-- The values of the section built from a raw family of values are that family. -/
private theorem DepProdSection.ofRaw_app (y : DepProdSectionRaw f Y A w) {A' : C} (h : A' ⟶ A)
    (v : V.obj (op A')) (hv : f.app (op A') v = W.map h.op w) :
    (DepProdSection.ofRaw y).app h v hv = y.app h v hv := by
  change (DepProdSection.ofRaw y).raw.app h v hv = _
  rw [DepProdSection.raw_ofRaw]

/-- The section with a given family of values. -/
noncomputable def DepProdSection.mk'
    (app : ∀ {A' : C} (h : A' ⟶ A) (v : V.obj (op A')),
      f.app (op A') v = W.map h.op w → Y.left.obj (op A'))
    (over : ∀ {A' : C} (h : A' ⟶ A) (v : V.obj (op A'))
      (hv : f.app (op A') v = W.map h.op w), Y.hom.app (op A') (app h v hv) = v)
    (naturality : ∀ {A₁ A₂ : C} (k : A₂ ⟶ A₁) (h : A₁ ⟶ A) (v : V.obj (op A₁))
      (hv : f.app (op A₁) v = W.map h.op w),
      Y.left.map k.op (app h v hv) = app (k ≫ h) (V.map k.op v) (map_compat f k h hv)) :
    DepProdSection f Y A w :=
  DepProdSection.ofRaw ⟨app, over, naturality⟩

/-- The values of the section built from a family of values are that family. -/
@[simp]
theorem DepProdSection.mk'_app
    (app : ∀ {A' : C} (h : A' ⟶ A) (v : V.obj (op A')),
      f.app (op A') v = W.map h.op w → Y.left.obj (op A'))
    (over : ∀ {A' : C} (h : A' ⟶ A) (v : V.obj (op A'))
      (hv : f.app (op A') v = W.map h.op w), Y.hom.app (op A') (app h v hv) = v)
    (naturality : ∀ {A₁ A₂ : C} (k : A₂ ⟶ A₁) (h : A₁ ⟶ A) (v : V.obj (op A₁))
      (hv : f.app (op A₁) v = W.map h.op w),
      Y.left.map k.op (app h v hv) = app (k ≫ h) (V.map k.op v) (map_compat f k h hv))
    {A' : C} (h : A' ⟶ A) (v : V.obj (op A'))
    (hv : f.app (op A') v = W.map h.op w) :
    (DepProdSection.mk' app over naturality).app h v hv = app h v hv :=
  DepProdSection.ofRaw_app _ h v hv

/-- Restriction of a section along `g : A₀ ⟶ A`. -/
noncomputable def DepProdSection.restrict (y : DepProdSection f Y A w) {A₀ : C} (g : A₀ ⟶ A) :
    DepProdSection f Y A₀ (W.map g.op w) :=
  DepProdSection.ofRaw (y.raw.restrict g)

/-- The value of the restriction of `y` along `g` at `h` is the value of `y` at `h ≫ g`. -/
@[simp]
theorem DepProdSection.restrict_app (y : DepProdSection f Y A w) {A₀ : C} (g : A₀ ⟶ A)
    {A' : C} (h : A' ⟶ A₀) (v : V.obj (op A'))
    (hv : f.app (op A') v = W.map h.op (W.map g.op w)) :
    (y.restrict g).app h v hv = y.app (h ≫ g) v (comp_compat f g h hv) :=
  DepProdSection.ofRaw_app _ h v hv

/-- The value of a restricted section at `h`, read off as the value of the original section at
any morphism equal to `h ≫ g`. -/
theorem DepProdSection.restrict_app_of_eq (y : DepProdSection f Y A w) {A₀ : C} (g : A₀ ⟶ A)
    {A' : C} (h : A' ⟶ A₀) (h' : A' ⟶ A) (hh : h' = h ≫ g) (v : V.obj (op A'))
    (hv : f.app (op A') v = W.map h.op (W.map g.op w))
    (hv' : f.app (op A') v = W.map h'.op w) :
    (y.restrict g).app h v hv = y.app h' v hv' := by
  subst hh
  rw [DepProdSection.restrict_app]

/-- A section of the dependent product of `Y₁`, pushed forward along a morphism `Y₁ ⟶ Y₂` over
`V`: the morphism is applied to all the values. -/
noncomputable def DepProdSection.mapOver {Y₁ Y₂ : Over V} (φ : Y₁ ⟶ Y₂)
    (y : DepProdSection f Y₁ A w) : DepProdSection f Y₂ A w :=
  DepProdSection.ofRaw
    { app := fun h v hv => φ.left.app _ (y.app h v hv)
      over := fun h v hv =>
        (hom_congr_apply (Over.w φ) _ (y.app h v hv)).trans (y.over h v hv)
      naturality := fun k h v hv =>
        (NatTrans.naturality_apply φ.left k.op (y.app h v hv)).symm.trans
          (congrArg (φ.left.app _) (y.naturality k h v hv)) }

/-- The values of `y.mapOver φ` are the images under `φ` of the values of `y`. -/
@[simp]
theorem DepProdSection.mapOver_app {Y₁ Y₂ : Over V} (φ : Y₁ ⟶ Y₂)
    (y : DepProdSection f Y₁ A w) {A' : C} (h : A' ⟶ A) (v : V.obj (op A'))
    (hv : f.app (op A') v = W.map h.op w) :
    (y.mapOver φ).app h v hv = φ.left.app (op A') (y.app h v hv) :=
  DepProdSection.ofRaw_app _ h v hv

end Small

/-! ### The dependent product presheaf -/

section Presheaf

variable [LocallySmall.{v₁} (Cᵒᵖ ⥤ Type v₁)]

variable (f)

/-- The sections of the dependent product of `Y` along `f` over `A`: pairs `(w, y)` with `w` a
section of `W` over `A` and `y` the family of values of a morphism `A ×_{w, W} V ⟶ Y` over `V`.

This is definitionally the sigma type `Σ w : W.obj A, DepProdSection f Y A.unop w`. -/
def DepProdSections (Y : Over V) (A : Cᵒᵖ) : Type v₁ :=
  Σ w : W.obj A, DepProdSection f Y A.unop w

/-- Sections of the dependent product are pairs, by definition. -/
theorem depProdSections_def (Y : Over V) (A : Cᵒᵖ) :
    DepProdSections f Y A = Σ w : W.obj A, DepProdSection f Y A.unop w :=
  rfl

/-- Two pairs `(w, y)` are equal as soon as the bases agree and all the values agree. -/
theorem depProdMk_ext {Y : Over V} {A : Cᵒᵖ} {w w' : W.obj A}
    {y : DepProdSection f Y A.unop w} {y' : DepProdSection f Y A.unop w'} (hw : w = w')
    (happ : ∀ (A' : C) (h : A' ⟶ A.unop) (v : V.obj (op A'))
      (hv : f.app (op A') v = W.map h.op w) (hv' : f.app (op A') v = W.map h.op w'),
      y.app h v hv = y'.app h v hv') :
    (⟨w, y⟩ : DepProdSections f Y A) = ⟨w', y'⟩ := by
  subst hw
  rw [show y = y' from DepProdSection.ext_app fun A' h v hv => happ A' h v hv hv]

/-- Transport of the value of a section along an equality of the pair `(w, y)`, of the morphism
`h` and of the section `v`. -/
theorem depProdSection_app_congr {Y : Over V} {A : Cᵒᵖ}
    {p q : DepProdSections f Y A} (hpq : p = q)
    {A' : C} {h h' : A' ⟶ A.unop} (hh : h = h') {v v' : V.obj (op A')} (hv₀ : v = v')
    (hv : f.app (op A') v = W.map h.op p.1) (hv' : f.app (op A') v' = W.map h'.op q.1) :
    p.2.app h v hv = q.2.app h' v' hv' := by
  subst hpq
  subst hh
  subst hv₀
  rfl

/-- The variant of `depProdSection_app_congr` in which the morphism is fixed. -/
theorem depProdSection_app_congr' {Y : Over V} {A : Cᵒᵖ}
    {p q : DepProdSections f Y A} (hpq : p = q) {A' : C} {v v' : V.obj (op A')} (hv₀ : v = v')
    (h : A' ⟶ A.unop) (hv : f.app (op A') v = W.map h.op p.1) :
    p.2.app h v hv = q.2.app h v' (by subst hpq; subst hv₀; exact hv) := by
  subst hpq
  subst hv₀
  rfl

/-- The dependent product of `Y : Over V` along `f : V ⟶ W`, as a presheaf: its sections over
`A` are the pairs `(w, y)` with `w` a section of `W` over `A` and `y` the family of values of a
morphism `A ×_{w, W} V ⟶ Y` over `V`. -/
noncomputable def depProdObj (Y : Over V) : Cᵒᵖ ⥤ Type v₁ where
  obj A := DepProdSections f Y A
  map g := ↾(fun p => ⟨W.map g p.1, p.2.restrict g.unop⟩)
  map_id := by
    intro A
    refine ConcreteCategory.ext_apply fun p => ?_
    obtain ⟨w, y⟩ := p
    change (⟨W.map (𝟙 A) w, y.restrict (𝟙 A).unop⟩ : DepProdSections f Y A) = ⟨w, y⟩
    refine depProdMk_ext f ?_ ?_
    · simp
    · intro A' h v hv hv'
      rw [DepProdSection.restrict_app]
      exact y.app_congr (Category.comp_id h) v _ _
  map_comp := by
    intro A₁ A₂ A₃ g₁ g₂
    refine ConcreteCategory.ext_apply fun p => ?_
    obtain ⟨w, y⟩ := p
    change (⟨W.map (g₁ ≫ g₂) w, y.restrict (g₁ ≫ g₂).unop⟩ : DepProdSections f Y A₃) =
      ⟨W.map g₂ (W.map g₁ w), (y.restrict g₁.unop).restrict g₂.unop⟩
    refine depProdMk_ext f ?_ ?_
    · change W.map (g₁ ≫ g₂) w = W.map g₂ (W.map g₁ w)
      simp
    · intro A' h v hv hv'
      rw [DepProdSection.restrict_app, DepProdSection.restrict_app,
        DepProdSection.restrict_app]
      exact y.app_congr (Category.assoc h g₂.unop g₁.unop).symm v _ _

/-- Restriction in `depProdObj f Y` along `g` restricts both the base section and the family
of values. -/
@[simp]
theorem depProdObj_map (Y : Over V) {A₁ A₂ : Cᵒᵖ} (g : A₁ ⟶ A₂)
    (p : (depProdObj f Y).obj A₁) :
    (depProdObj f Y).map g p = ⟨W.map g p.1, p.2.restrict g.unop⟩ :=
  rfl

/-- The structure morphism of the dependent product: it reads off the base section `w`. -/
noncomputable def depProdπ (Y : Over V) : depProdObj f Y ⟶ W where
  app _ := ↾(fun p => p.1)
  naturality := by intros; ext p; rfl

/-- The structure morphism `depProdπ f Y` sends a pair `(w, y)` to `w`. -/
@[simp]
theorem depProdπ_app (Y : Over V) (A : Cᵒᵖ) (p : (depProdObj f Y).obj A) :
    (depProdπ f Y).app A p = p.1 :=
  rfl

/-- Functoriality of the dependent product in `Y`: a morphism `Y₁ ⟶ Y₂` over `V` is applied to
all the values. -/
noncomputable def depProdObjMap {Y₁ Y₂ : Over V} (φ : Y₁ ⟶ Y₂) :
    depProdObj f Y₁ ⟶ depProdObj f Y₂ where
  app _ := ↾(fun p => ⟨p.1, p.2.mapOver φ⟩)
  naturality := by
    intro A₁ A₂ g
    refine ConcreteCategory.ext_apply fun p => ?_
    obtain ⟨w, y⟩ := p
    change (⟨W.map g w, (y.restrict g.unop).mapOver φ⟩ : DepProdSections f Y₂ A₂) =
      ⟨W.map g w, (y.mapOver φ).restrict g.unop⟩
    refine depProdMk_ext f rfl ?_
    intro A' h v hv hv'
    rw [DepProdSection.mapOver_app, DepProdSection.restrict_app, DepProdSection.restrict_app,
      DepProdSection.mapOver_app]

/-- The values of the image of a section under `depProdObjMap f φ` are the images under `φ` of
its values. -/
@[simp]
theorem depProdObjMap_app {Y₁ Y₂ : Over V} (φ : Y₁ ⟶ Y₂) (A : Cᵒᵖ) (p : (depProdObj f Y₁).obj A)
    {A' : C} (h : A' ⟶ A.unop) (v : V.obj (op A'))
    (hv : f.app (op A') v = W.map h.op p.1) :
    ((depProdObjMap f φ).app A p).2.app h v hv = φ.left.app (op A') (p.2.app h v hv) :=
  DepProdSection.mapOver_app φ p.2 h v hv

/-- The dependent product (Weil restriction) along `f : V ⟶ W`, as a functor
`Over V ⥤ Over W`. -/
@[sga "3 III 0.1.1" "more general", sga "4 IV 5.2" "c), special case"]
noncomputable def depProd : Over V ⥤ Over W where
  obj Y := Over.mk (depProdπ f Y)
  map φ := Over.homMk (depProdObjMap f φ) (by ext; rfl)
  map_id := by
    intro Y
    ext A p
    change (⟨p.1, p.2.mapOver (𝟙 Y)⟩ : DepProdSections f Y A) = ⟨p.1, p.2⟩
    refine depProdMk_ext f rfl ?_
    intro A' h v hv hv'
    rw [DepProdSection.mapOver_app]
    rfl
  map_comp := by
    intro Y₁ Y₂ Y₃ φ ψ
    ext A p
    change (⟨p.1, p.2.mapOver (φ ≫ ψ)⟩ : DepProdSections f Y₃ A) =
      ⟨p.1, (p.2.mapOver φ).mapOver ψ⟩
    refine depProdMk_ext f rfl ?_
    intro A' h v hv hv'
    rw [DepProdSection.mapOver_app, DepProdSection.mapOver_app, DepProdSection.mapOver_app]
    rfl

/-- The underlying presheaf of `(depProd f).obj Y` is `depProdObj f Y`. -/
@[simp]
theorem depProd_obj_left (Y : Over V) : ((depProd f).obj Y).left = depProdObj f Y :=
  rfl

/-- The structure morphism of `(depProd f).obj Y` is `depProdπ f Y`. -/
@[simp]
theorem depProd_obj_hom (Y : Over V) : ((depProd f).obj Y).hom = depProdπ f Y :=
  rfl

/-- The underlying morphism of presheaves of `(depProd f).map φ` is `depProdObjMap f φ`. -/
@[simp]
theorem depProd_map_left {Y₁ Y₂ : Over V} (φ : Y₁ ⟶ Y₂) :
    ((depProd f).map φ).left = depProdObjMap f φ :=
  rfl

end Presheaf

section Counit

variable [LocallySmall.{v₁} (Cᵒᵖ ⥤ Type v₁)]

variable (f) (Y : Over V)

/-- The compatibility datum carried by a section of the base change of the dependent product:
the `V`-component lies over the base section read off by the `depProd`-component. -/
theorem counit_compat {A : Cᵒᵖ} (e : (Limits.pullback (depProdπ f Y) f).obj A) :
    f.app (op A.unop) ((Limits.pullback.snd (depProdπ f Y) f).app A e) =
      W.map (𝟙 A.unop).op (((Limits.pullback.fst (depProdπ f Y) f).app A e).1) := by
  have hw : W.map (𝟙 A.unop).op (((Limits.pullback.fst (depProdπ f Y) f).app A e).1)
      = ((Limits.pullback.fst (depProdπ f Y) f).app A e).1 := by simp
  rw [hw]
  exact (hom_congr_apply (Limits.pullback.condition (f := depProdπ f Y) (g := f)) A e).symm

/-- The counit (evaluation map) of the dependent-product adjunction: a section of the base
change of `depProd f Y` is a pair `(⟨w, y⟩, v)` with `f v = w`, and it is sent to the value that
`y` takes at the identity and at `v`. -/
noncomputable def depProdCounitApp : (Over.pullback f).obj ((depProd f).obj Y) ⟶ Y :=
  Over.homMk
    { app := fun A => ↾(fun e =>
        ((Limits.pullback.fst (depProdπ f Y) f).app A e).2.app (𝟙 A.unop)
          ((Limits.pullback.snd (depProdπ f Y) f).app A e) (counit_compat f Y e))
      naturality := by
        intro A₁ A₂ g
        refine ConcreteCategory.ext_apply fun e => ?_
        have hc := counit_compat f Y e
        have hfst : (Limits.pullback.fst (depProdπ f Y) f).app A₂
              ((Limits.pullback (depProdπ f Y) f).map g e)
            = (depProdObj f Y).map g ((Limits.pullback.fst (depProdπ f Y) f).app A₁ e) :=
          NatTrans.naturality_apply (Limits.pullback.fst (depProdπ f Y) f) g e
        have hsnd : (Limits.pullback.snd (depProdπ f Y) f).app A₂
              ((Limits.pullback (depProdπ f Y) f).map g e)
            = V.map g ((Limits.pullback.snd (depProdπ f Y) f).app A₁ e) :=
          NatTrans.naturality_apply (Limits.pullback.snd (depProdπ f Y) f) g e
        refine Eq.trans (depProdSection_app_congr f hfst rfl hsnd _ ?_) ?_
        · exact (map_compat f g.unop (𝟙 A₁.unop) hc).trans (by simp)
        · refine Eq.trans (DepProdSection.restrict_app_of_eq
            ((Limits.pullback.fst (depProdπ f Y) f).app A₁ e).2 g.unop (𝟙 A₂.unop)
            (g.unop ≫ 𝟙 A₁.unop) (by simp) _ _
            (map_compat f g.unop (𝟙 A₁.unop) hc)) ?_
          exact (((Limits.pullback.fst (depProdπ f Y) f).app A₁ e).2.naturality
            g.unop (𝟙 A₁.unop) ((Limits.pullback.snd (depProdπ f Y) f).app A₁ e) hc).symm }
    (by
      ext A e
      exact ((Limits.pullback.fst (depProdπ f Y) f).app A e).2.over _ _ _)

/-- The counit sends a section `(⟨w, y⟩, v)` of the base change of `depProd f Y` to the value
of `y` at the identity and at `v`. -/
@[simp]
theorem depProdCounitApp_left_app {A : Cᵒᵖ} (e : (Limits.pullback (depProdπ f Y) f).obj A) :
    (depProdCounitApp f Y).left.app A e =
      ((Limits.pullback.fst (depProdπ f Y) f).app A e).2.app (𝟙 A.unop)
        ((Limits.pullback.snd (depProdπ f Y) f).app A e) (counit_compat f Y e) :=
  rfl

end Counit

end CategoryTheory.Presheaf

end
