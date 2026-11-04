module

public import StacksFrontier.AlgebraicGeometry.Descent.Parasitic.FlatCohomologyBaseChange

/-!
# Reading the comparison map at the identity chart of a small Zariski site

Let `B` be a big fppf site, `S` a scheme below its cutoff and `φ : ℱ ⟶ 𝒢` a morphism of sheaves
of `𝒪`-modules on `(Sch/S)_fppf`.  Its restriction `φ|_{X_Zar}` to the small Zariski site of the
scheme `X` of an object `T` of the site is an isomorphism exactly when `φ` is an isomorphism on
sections over the objects `(V ↪ X → S)` for all opens `V` of `X`; the open `V = ⊤` gives an object
isomorphic to `T` itself, so an isomorphic restriction makes `φ` an isomorphism on sections over
`T`.

That is the step described as *reading clause (2) of [Stacks, Tag 0756] at the identity chart
of `U_τ`* in the documentation of the sectionwise forms of the comparison step,
`AlgebraicGeometry.bigFppfCohomology_map_bijective_of_isIso_sections` and
`AlgebraicGeometry.BigFppfOver.bigFppfCohomology_zariskiComparisonMap_bijective`: they carry the
sectionwise hypothesis `IsIso (φ.val.app (op U))`, while clause (2) of the source is about the
restricted sheaves `g^*_{τ,small}(𝒢|_{S_τ})` and `𝒢|_{U_τ}`.  This file proves the passage from
the restricted form to the sectionwise one, and restates the comparison step of
`AlgebraicGeometry.bigFppfCohomology_map_bijective_of_isIso_sections` with its hypothesis in the
restricted form.

## Main results

* `Stacks.SheafOfModules.bijective_val_map_of_isoObj` and
  `Stacks.SheafOfModules.bijective_val_app_of_isoObj`: sections of a sheaf of modules along an
  isomorphism of objects are bijective, and bijectivity of a morphism on sections only depends on
  the isomorphism class of the object.
* `AlgebraicGeometry.BigFppfOver.objTopChartIso`: the object `(⊤ ↪ X → S)` attached to the whole
  of the scheme `X` of an object `T` is isomorphic to `T`.  Both are final in the localization of
  `(Sch/S)_fppf` at `T`.
* `AlgebraicGeometry.BigFppfOver.isIso_val_app_of_isIso_zariskiRestriction`: **if `φ|_{X_Zar}` is
  an isomorphism then `φ` is an isomorphism on sections over `T`.**
* `AlgebraicGeometry.bigFppfCohomology_map_bijective_of_isIso_zariskiRestriction`: the comparison
  step of [Stacks, Tag 0756] which rests on [Stacks, Tag 0755], with its hypothesis in the
  restricted form: if `φ|_{Y_Zar}` is an isomorphism for every object `Y` flat and locally of
  finite presentation over `S`, then `H^p(U, ℱ) → H^p(U, 𝒢)` is bijective for every such `U` and
  every `p`.

## Implementation notes

The restriction `𝒢 ↦ 𝒢|_{X_Zar}` here is `objRestrict` followed by `restrictModule`, which is the
spelling `AlgebraicGeometry.BigFppfOver.objZariskiRestrict` and
`AlgebraicGeometry.BigFppfOver.zariskiComparisonRestrictIso` use; it is the same functor as the
`AlgebraicGeometry.BigFppfOver.objZariskiPushforward` that the base-change map of clause (2) is
stated with, by `AlgebraicGeometry.BigFppfOver.objZariskiRestrictIso`.

Each of the three functors composing it is a `CategoryTheory.SheafOfModules.pushforward`, whose
sections over an object are literally the sections of the original over the image object.  So the
sections of `φ|_{X_Zar}` over an open `V` of `X` *are* `φ.val.app` at
`(Over.forget T).obj ((objEquiv B S hS T).functor.obj (opensObj B X hX V))`, the object
`(V ↪ X → S)`, and no transport appears in the statements below — only the isomorphism between
that object at `V = ⊤` and `T`.

That isomorphism is the uniqueness of final objects in the localization at `T`: the open `⊤` of
`X` is final in the big fppf site of `X` by
`AlgebraicGeometry.BigFppfOver.isTerminalOpensObjTop`, the equivalence
`AlgebraicGeometry.BigFppfOver.objEquiv` of Stacks 06WI carries it to a final object of the
localization, and `T` itself is final there.

The converse — that a `φ` which is an isomorphism on sections over every `(V ↪ X → S)` has
isomorphic restriction — is not needed here; it follows from
`Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_val_app` applied to the same
definitional identification of the sections.

**No `@[stacks 0756]` attribute is placed here.**  What is proved below is a bridge between two
shapes of the *hypothesis* of the comparison step, not the conclusion of [Stacks, Tag 0756].  That
conclusion is `AlgebraicGeometry.BigFppfOver.flatSmallSiteCohomologyAddEquiv` at `τ = Zariski`
and `AlgebraicGeometry.BigFppfOver.flatSmallEtaleSiteCohomologyAddEquiv` at `τ = étale`, in both
cases for a general `U`; the statement below is used on the way, through
`AlgebraicGeometry.BigFppfOver.zariskiSmallSiteCohomologyAddEquiv`.

Clause (2) gives the hypothesis of the statements below because, under clause (1), the canonical
map `AlgebraicGeometry.BigFppfOver.zariskiClause2Map` of clause (2) is
`AlgebraicGeometry.BigFppfOver.zariskiComparisonRestrictIso` followed by the restriction of the
comparison map (`AlgebraicGeometry.BigFppfOver.zariskiClause2Map_eq`), and the adjoint-transpose
spelling `AlgebraicGeometry.BigFppfOver.zariskiBaseChangeMap` is that map followed by an
isomorphism (`AlgebraicGeometry.BigFppfOver.zariskiBaseChangeMap_eq`).

## References

* [Stacks Project, Tag 0756](https://stacks.math.columbia.edu/tag/0756)
* [Stacks Project, Tag 0755](https://stacks.math.columbia.edu/tag/0755)
* [Stacks Project, Tag 06WI](https://stacks.math.columbia.edu/tag/06WI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u w v₁ u₁

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- **Restriction of sections along an isomorphism of objects is bijective.**  The restriction
along the inverse isomorphism is a two-sided inverse, by functoriality of the sections. -/
public theorem bijective_val_map_of_isoObj (M : SheafOfModules.{u} R) {A A' : C} (e : A ≅ A') :
    Function.Bijective (M.val.map e.hom.op) := by
  have hid : ∀ {X : Cᵒᵖ} (y : M.val.obj X), M.val.map (𝟙 X) y = y := by
    intro X y
    simp only [PresheafOfModules.map_id]
    exact ModuleCat.restrictScalarsId'App_inv_apply _ (by simp) _ y
  have key : ∀ {A A' : C} (e : A ≅ A') (x : M.val.obj (op A')),
      M.val.map e.inv.op (M.val.map e.hom.op x) = x := fun e x => by
    have h : e.hom.op ≫ e.inv.op = 𝟙 _ := by rw [← op_comp, e.inv_hom_id, op_id]
    exact (PresheafOfModules.map_comp_apply M.val e.hom.op e.inv.op x).symm.trans
      ((M.val.congr_map_apply h x).trans (hid x))
  exact Function.bijective_iff_has_inverse.mpr
    ⟨M.val.map e.inv.op, key e, key e.symm⟩

/-- **Bijectivity of a morphism of sheaves of modules on sections over an object depends only on
the isomorphism class of the object.**  The two sections maps are conjugate by the restrictions
along the isomorphism, which are bijective. -/
public theorem bijective_val_app_of_isoObj {M N : SheafOfModules.{u} R} (φ : M ⟶ N)
    {A A' : C} (e : A ≅ A') (h : Function.Bijective (φ.val.app (op A))) :
    Function.Bijective (φ.val.app (op A')) := by
  have hM : Function.Bijective (M.val.map e.hom.op) := bijective_val_map_of_isoObj M e
  have hN : Function.Bijective (N.val.map e.hom.op) := bijective_val_map_of_isoObj N e
  have hcomp : Function.Bijective
      ((N.val.map e.hom.op) ∘ (φ.val.app (op A'))) := by
    have hfun : (N.val.map e.hom.op) ∘ (φ.val.app (op A')) =
        (φ.val.app (op A)) ∘ (M.val.map e.hom.op) := by
      funext x
      exact (PresheafOfModules.naturality_apply φ.val e.hom.op x).symm
    rw [hfun]
    exact h.comp hM
  exact (Function.Bijective.of_comp_iff' hN _).mp hcomp

end Stacks.SheafOfModules

namespace AlgebraicGeometry.BigFppfOver

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (T : BigFppfOver B S hS)

/-- **The object `(V ↪ X → S)` of the big fppf site over `S`** attached to an open `V` of the
scheme `X` of an object `T`: the open read in the big fppf site of `X`, carried into the
localization at `T` by the equivalence of Stacks 06WI, and then read over `S`.

This is the object over which the sections of `𝒢|_{X_Zar}` over `V` are taken: all three functors
composing `objRestrict ⋙ restrictModule` are pushforwards of sheaves of modules, so the sections
over `V` are the sections of `𝒢` over this object. -/
public abbrev objOpensChart (V : (objScheme B S hS T).Opens) : BigFppfOver B S hS :=
  (Over.forget T).obj ((objEquiv B S hS T).functor.obj
    (opensObj B (objScheme B S hS T) (contains_objScheme B S hS T) V))

/-- The identity chart `(⊤ ↪ X → S)` of the small Zariski site of the scheme `X` of `T`. -/
public abbrev objTopChart : BigFppfOver B S hS := objOpensChart B S hS T ⊤

/-- The identity chart is a final object of the localization of `(Sch/S)_fppf` at `T`: the open
`⊤` of `X` is final in the big fppf site of `X`, and the equivalence of Stacks 06WI preserves
final objects. -/
public def isTerminal_objEquiv_opensObjTop :
    IsTerminal ((objEquiv B S hS T).functor.obj
      (opensObj B (objScheme B S hS T) (contains_objScheme B S hS T) ⊤)) :=
  IsTerminal.isTerminalObj (objEquiv B S hS T).functor _
    (isTerminalOpensObjTop B (objScheme B S hS T) (contains_objScheme B S hS T))

/-- **The identity chart `(⊤ ↪ X → S)` is isomorphic to `T`.**  Both are final objects of the
localization of `(Sch/S)_fppf` at `T`, so the unique morphisms between them are mutually inverse;
the isomorphism of objects over `S` is the image of that one under
`CategoryTheory.Over.forget`. -/
public def objTopChartIso : objTopChart B S hS T ≅ T :=
  (Over.forget T).mapIso
    ((isTerminal_objEquiv_opensObjTop B S hS T).uniqueUpToIso Over.mkIdTerminal)

/-- **If the restriction of `φ` to the small Zariski site of the scheme `X` of `T` is an
isomorphism, then `φ` is an isomorphism on sections over `T`.**

An isomorphism of sheaves of modules on `X_Zar` is bijective on sections over the open `⊤` of
`X`, and those sections are the sections of `φ` over the identity chart `(⊤ ↪ X → S)`, which is
isomorphic to `T` by `AlgebraicGeometry.BigFppfOver.objTopChartIso`.

Read at `T` of the form `U → S` with `U` flat and locally of finite presentation over `S`, this
is the passage from the restricted form of clause (2) of [Stacks, Tag 0756] to the sectionwise
hypothesis of `AlgebraicGeometry.bigFppfCohomology_map_bijective_of_isIso_sections`. -/
public theorem isIso_val_app_of_isIso_zariskiRestriction
    {F G : SheafOfModules.{u} (structureSheaf B S hS)} (φ : F ⟶ G)
    (hφ : IsIso ((restrictModule B (objScheme B S hS T) (contains_objScheme B S hS T)).map
      ((objRestrict B S hS T).map φ))) :
    IsIso (φ.val.app (op T)) := by
  have h₁ : Function.Bijective
      (((restrictModule B (objScheme B S hS T) (contains_objScheme B S hS T)).map
        ((objRestrict B S hS T).map φ)).val.app
          (op (⊤ : (objScheme B S hS T).Opens))) :=
    _root_.SheafOfModules.bijective_val_app_of_isIso _ hφ _
  -- The sections of `φ|_{X_Zar}` over `⊤` are those of `φ` over the identity chart by unfolding
  -- three pushforwards and the equivalence of Stacks 06WI; the image object is named one functor
  -- at a time (`opensToBig`, `Over.iteratedSliceBackward`, `Over.forget`), since the unfolding in
  -- a single step exceeds the heartbeat budget.
  have h₂ : Function.Bijective
      (((objRestrict B S hS T).map φ).val.app
        (op ((opensToBig B (objScheme B S hS T) (contains_objScheme B S hS T)).obj ⊤))) := h₁
  have h₃ : Function.Bijective
      (((objRestrictFunctor B S hS T).map
          ((SheafOfModules.overFunctor (structureSheaf B S hS) T).map φ)).val.app
        (op ((opensToBig B (objScheme B S hS T) (contains_objScheme B S hS T)).obj ⊤))) := h₂
  have h₄ : Function.Bijective
      (((SheafOfModules.overFunctor (structureSheaf B S hS) T).map φ).val.app
        (op ((Over.iteratedSliceBackward T).obj
          ((opensToBig B (objScheme B S hS T) (contains_objScheme B S hS T)).obj ⊤)))) := h₃
  have h₀ : Function.Bijective (φ.val.app (op (objTopChart B S hS T))) := h₄
  exact (ConcreteCategory.isIso_iff_bijective _).2
    (Stacks.SheafOfModules.bijective_val_app_of_isoObj φ (objTopChartIso B S hS T) h₀)

end AlgebraicGeometry.BigFppfOver

namespace AlgebraicGeometry

/-- **The comparison step of [Stacks, Tag 0756] which rests on [Stacks, Tag 0755], with its
hypothesis read on the small Zariski sites.**  Let `φ : ℱ ⟶ 𝒢` be a morphism of sheaves of
modules on `(Sch/S)_fppf` whose restriction `φ|_{Y_Zar}` to the small Zariski site of the scheme
of `Y` is an isomorphism for every object `Y` of the site flat and locally of finite presentation
over `S`.  Then

  `H^p(U, ℱ) → H^p(U, 𝒢)`

is bijective for every such `U` and every `p`.

This is `AlgebraicGeometry.bigFppfCohomology_map_bijective_of_isIso_sections` with its sectionwise
hypothesis supplied by `AlgebraicGeometry.BigFppfOver.isIso_val_app_of_isIso_zariskiRestriction`.
The hypothesis here is the shape clause (2) of the source has — an isomorphism of restricted
sheaves on `U_τ` rather than of the sections over `U`.

What this does **not** assert is any part of the conclusion of [Stacks, Tag 0756]: the
identification of `H^p(U, ℱ)` with the small-site cohomology `H^p(U, 𝒢|_{U_τ})` by
[Stacks, Tag 03DW].  The hypothesis is supplied by clauses (1) and (2) of the source through
`AlgebraicGeometry.BigFppfOver.isIso_objZariskiRestrict_map_zariskiComparisonMap`.  No
`@[stacks 0756]` attribute is placed here. -/
public theorem bigFppfCohomology_map_bijective_of_isIso_zariskiRestriction
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    [HasSheafify (AlgebraicGeometry.BigFppfOver.topology B S hS) AddCommGrpCat.{u}]
    [(AlgebraicGeometry.BigFppfOver.topology B S hS).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [HasExt.{w} (Sheaf (AlgebraicGeometry.BigFppfOver.topology B S hS) AddCommGrpCat.{u})]
    {F G : SheafOfModules.{u} (AlgebraicGeometry.BigFppfOver.structureSheaf B S hS)} (φ : F ⟶ G)
    (hφ : ∀ Y : AlgebraicGeometry.BigFppfOver B S hS,
      Flat ((Over.post B.inclusion).obj Y).hom →
      LocallyOfFinitePresentation ((Over.post B.inclusion).obj Y).hom →
      IsIso ((BigFppfOver.restrictModule B (BigFppfOver.objScheme B S hS Y)
        (BigFppfOver.contains_objScheme B S hS Y)).map
          ((BigFppfOver.objRestrict B S hS Y).map φ)))
    (U : AlgebraicGeometry.BigFppfOver B S hS)
    (hU : Flat ((Over.post B.inclusion).obj U).hom ∧
      LocallyOfFinitePresentation ((Over.post B.inclusion).obj U).hom) (p : ℕ) :
    Function.Bijective
      (Stacks.Cohomology.LongExactSequence.map.{w}
        ((SheafOfModules.toSheaf (AlgebraicGeometry.BigFppfOver.structureSheaf B S hS)).map φ)
          p U) :=
  bigFppfCohomology_map_bijective_of_isIso_sections B S hS φ
    (fun Y h₁ h₂ =>
      BigFppfOver.isIso_val_app_of_isIso_zariskiRestriction B S hS Y φ (hφ Y h₁ h₂)) U hU p

end AlgebraicGeometry

end
