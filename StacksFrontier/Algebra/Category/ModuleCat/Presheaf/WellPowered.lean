module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Submodule
public import Mathlib.Algebra.Category.ModuleCat.Subobject

/-!
# Presheaves of modules are well-powered, at independent universes

Let `R : Cᵒᵖ ⥤ RingCat.{u}` be a presheaf of rings on a category `C : Type u₁` with
morphisms in `Type v₁`, and let `M : PresheafOfModules.{v} R`. We show that the
subobjects of `M` in `PresheafOfModules.{v} R` are exactly the families of submodules
of the `M.obj X` that are stable under restriction, i.e. the terms of
`PresheafOfModules.Submodule M`. Since that type lives in `Type (max u₁ v)`, this
gives `WellPowered.{max u₁ v} (PresheafOfModules.{v} R)` with the ring universe `u` and
the morphism universe `v₁` of the site completely free.

Mathlib has `PresheafOfModules.wellPowered`, but only in the totally collapsed case: it
requires `C₀ : Type u` with `[SmallCategory C₀]` and `R₀ : C₀ᵒᵖ ⥤ RingCat.{u}`, and
concludes `WellPowered.{u} (PresheafOfModules.{u} R₀)`. All four universes (objects and
morphisms of the site, sections of the ring, sections of the module) are the same `u`
there. That is forced by the route it takes, not by the mathematics: it deduces
well-poweredness from the detecting family `PresheafOfModules.freeYoneda R₀`, whose
objects are `(free R₀).obj (yoneda.obj X)`; `PresheafOfModules.free` only exists as
`(Cᵒᵖ ⥤ Type u) ⥤ PresheafOfModules.{u} R` for `R : Cᵒᵖ ⥤ RingCat.{u}` (the free module
functor pins the ring universe to the module universe), and `yoneda.obj X` is a presheaf
of types in the morphism universe (which pins that one too).

The route taken here avoids the free module functor entirely, so none of those
identifications arise.

## Main definitions

* `PresheafOfModules.Submodule.range`: the family of pointwise `LinearMap.range`s of a
  morphism of presheaves of modules, as a `PresheafOfModules.Submodule` of the target.
* `PresheafOfModules.factorThru`: the factorization of `f : M₁ ⟶ M` through a
  monomorphism `g : M₂ ⟶ M` whose pointwise ranges dominate those of `f`.
* `PresheafOfModules.subobjectSubmodule`: the order isomorphism between `Subobject M`
  and `PresheafOfModules.Submodule M`.

## Main results

* `PresheafOfModules.mk_le_mk_iff_range_le`: two subobjects presented by monomorphisms
  are comparable exactly when their pointwise ranges are.
* `PresheafOfModules.wellPowered'`: `WellPowered.{max u₁ v} (PresheafOfModules.{v} R)`,
  for `C : Type u₁` with `[Category.{v₁} C]` and `R : Cᵒᵖ ⥤ RingCat.{u}`.

## Implementation notes

What is forced and what is chosen:

* The bound `max u₁ v` is forced and is optimal: `PresheafOfModules.Submodule M` is a
  family indexed by `Cᵒᵖ : Type u₁` of submodules of the `M.obj X : Type v`, and the
  morphisms of `PresheafOfModules.{v} R` live in `Type (max u₁ v)` as well, so
  `LocallySmall.{max u₁ v}` (needed even to state `WellPowered.{max u₁ v}`) is the
  sharpest available. The ring universe `u` and the morphism universe `v₁` of the site do
  not enter, which is the whole point of the file.
* The name `wellPowered'` is primed because Mathlib's `PresheafOfModules.wellPowered` is
  already in scope in the same namespace; the two are not comparable instances (neither
  universe signature is an instance of the other), so both are kept.
* The factorization `factorThru` is built pointwise from
  `LinearEquiv.ofInjective` on the monomorphism `g`, whose pointwise injectivity comes
  from `PresheafOfModules.injective_of_mono`. Its naturality square is proved by
  composing with `g` and using injectivity; the chain is written in term mode on purpose,
  because `rw` cannot be used across the `ModuleCat.restrictScalars` coercion that the
  naturality field of `PresheafOfModules.Hom` carries (`kabstract` reports the target as
  not type-correct under `implicit` transparency).

## References

This is the smallness input to
[Stacks Project, Tag 040B](https://stacks.math.columbia.edu/tag/040B) (the isomorphism
classes of invertible modules on a ringed site form a set), whose site, morphism and
section universes are independent; see also
[Stacks Project, Tag 01CW](https://stacks.math.columbia.edu/tag/01CW).
-/

@[expose] public section

universe v v₁ u₁ u

open CategoryTheory Limits

namespace PresheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {R : Cᵒᵖ ⥤ RingCat.{u}}

section Range

variable {M₀ M₁ M₂ M : PresheafOfModules.{v} R}

/-- The family of pointwise ranges of a morphism of presheaves of modules. It is stable
under restriction by naturality, hence is a `PresheafOfModules.Submodule` of the target. -/
def Submodule.range (f : M₁ ⟶ M₂) : M₂.Submodule where
  obj X := LinearMap.range (Hom.app f X).hom
  map {_ _} g := by
    rintro x ⟨p, rfl⟩
    exact ⟨M₁.map g p, by simpa using naturality_apply f g p⟩

/-- The value of `Submodule.range f` at `X` is the range of `f` at `X`. -/
@[simp]
lemma Submodule.range_obj (f : M₁ ⟶ M₂) (X : Cᵒᵖ) :
    (Submodule.range f).obj X = LinearMap.range (Hom.app f X).hom :=
  rfl

/-- The range of the inclusion `N.ι` of a submodule `N` is `N` itself. -/
@[simp]
lemma Submodule.range_ι (N : M.Submodule) : Submodule.range N.ι = N := by
  refine Submodule.ext fun X => ?_
  rw [Submodule.range_obj,
    show (Hom.app N.ι X).hom = (N.obj X).subtype from rfl]
  exact _root_.Submodule.range_subtype _

/-- The range of a composite `f ≫ g` is contained in the range of `g`. -/
lemma Submodule.range_comp_le (f : M₁ ⟶ M₂) (g : M₂ ⟶ M) :
    Submodule.range (f ≫ g) ≤ Submodule.range g := fun X => by
  simpa only [Submodule.range_obj, comp_app, ModuleCat.hom_comp] using
    LinearMap.range_comp_le_range (Hom.app f X).hom (Hom.app g X).hom

/-- Precomposing with an isomorphism does not change the range. -/
lemma Submodule.range_isIso_comp (i : M₀ ⟶ M₁) [IsIso i] (g : M₁ ⟶ M) :
    Submodule.range (i ≫ g) = Submodule.range g := by
  refine Submodule.ext fun X => ?_
  rw [Submodule.range_obj, Submodule.range_obj, comp_app, ModuleCat.hom_comp,
    LinearMap.range_comp, LinearMap.range_eq_top.2 (surjective_of_epi i X),
    _root_.Submodule.map_top]

end Range

section FactorThru

variable {M₁ M₂ M : PresheafOfModules.{v} R} (f : M₁ ⟶ M) (g : M₂ ⟶ M) [Mono g]
  (h : Submodule.range f ≤ Submodule.range g)

/-- The value at `X` of the factorization of `f` through the monomorphism `g`. -/
noncomputable def factorThruApp (X : Cᵒᵖ) : M₁.obj X ⟶ M₂.obj X :=
  ModuleCat.ofHom
    ((LinearEquiv.ofInjective (Hom.app g X).hom (injective_of_mono g X)).symm.toLinearMap ∘ₗ
      LinearMap.codRestrict _ (Hom.app f X).hom fun a => h X ⟨a, rfl⟩)

/-- The component `factorThruApp f g h X` composed with `g` at `X` is `f` at `X`. -/
@[simp]
lemma app_factorThruApp (X : Cᵒᵖ) (a : M₁.obj X) :
    Hom.app g X (factorThruApp f g h X a) = Hom.app f X a :=
  congrArg Subtype.val
    ((LinearEquiv.ofInjective (Hom.app g X).hom (injective_of_mono g X)).apply_symm_apply
      (LinearMap.codRestrict _ (Hom.app f X).hom (fun a => h X ⟨a, rfl⟩) a))

/-- The components `factorThruApp f g h` commute with the restriction maps of `M₁` and `M₂`. -/
lemma factorThruApp_naturality {X Y : Cᵒᵖ} (u : X ⟶ Y) (a : M₁.obj X) :
    factorThruApp f g h Y (M₁.map u a) = M₂.map u (factorThruApp f g h X a) :=
  injective_of_mono g Y
    ((app_factorThruApp f g h Y (M₁.map u a)).trans
      ((naturality_apply f u a).trans
        ((congrArg (fun z : M.obj X => M.map u z) (app_factorThruApp f g h X a)).symm.trans
          (naturality_apply g u (factorThruApp f g h X a)).symm)))

/-- The factorization of `f : M₁ ⟶ M` through a monomorphism `g : M₂ ⟶ M` whose pointwise
ranges contain those of `f`. -/
noncomputable def factorThru : M₁ ⟶ M₂ where
  app := factorThruApp f g h
  naturality u := by
    ext a
    exact factorThruApp_naturality f g h u a

/-- The factorization `factorThru f g h` composed with `g` is `f`. -/
@[reassoc (attr := simp)]
lemma factorThru_comp : factorThru f g h ≫ g = f := by
  ext X a
  exact app_factorThruApp f g h X a

end FactorThru

section Subobject

variable {M : PresheafOfModules.{v} R}

/-- Two subobjects of a presheaf of modules, presented by monomorphisms, are comparable
exactly when their families of pointwise ranges are. -/
lemma mk_le_mk_iff_range_le {M₁ M₂ : PresheafOfModules.{v} R} (f : M₁ ⟶ M) (g : M₂ ⟶ M)
    [Mono f] [Mono g] :
    Subobject.mk f ≤ Subobject.mk g ↔ Submodule.range f ≤ Submodule.range g :=
  ⟨fun hle =>
      (congrArg Submodule.range (Subobject.ofMkLEMk_comp hle)).symm.trans_le
        (Submodule.range_comp_le (Subobject.ofMkLEMk f g hle) g),
    fun hle => Subobject.mk_le_mk_of_comm _ (factorThru_comp f g hle)⟩

/-- The arrow of the subobject `Subobject.mk f` has the same range as the monomorphism `f`. -/
@[simp]
lemma Submodule.range_mk_arrow {M₁ : PresheafOfModules.{v} R} (f : M₁ ⟶ M) [Mono f] :
    Submodule.range (Subobject.mk f).arrow = Submodule.range f :=
  (Submodule.range_isIso_comp (Subobject.underlyingIso f).inv (Subobject.mk f).arrow).symm.trans
    (congrArg Submodule.range (Subobject.underlyingIso_arrow f))

/-- The subobjects of a presheaf of modules `M` are exactly the families of submodules of
the `M.obj X` stable under restriction. This is the presheaf-of-modules analogue of
`ModuleCat.subobjectModule`, and unlike the route through the free module functor it
leaves the ring universe and the morphism universe of the site free. -/
noncomputable def subobjectSubmodule (M : PresheafOfModules.{v} R) :
    Subobject M ≃o M.Submodule where
  toFun P := Submodule.range P.arrow
  invFun N := Subobject.mk N.ι
  left_inv P :=
    Eq.trans
      (le_antisymm ((mk_le_mk_iff_range_le _ _).2 (by simp))
        ((mk_le_mk_iff_range_le _ _).2 (by simp)))
      (Subobject.mk_arrow P)
  right_inv N := by simp
  map_rel_iff' {P Q} :=
    (mk_le_mk_iff_range_le P.arrow Q.arrow).symm.trans
      (by rw [Subobject.mk_arrow, Subobject.mk_arrow])

/-- Presheaves of modules are well-powered with the universe of the sections of the ring
and the universe of the morphisms of the site both free. Compare Mathlib's
`PresheafOfModules.wellPowered`, which collapses all four universes to one. -/
instance wellPowered' : WellPowered.{max u₁ v} (PresheafOfModules.{v} R) where
  subobject_small M := small_of_injective (subobjectSubmodule M).injective

end Subobject

end PresheafOfModules
