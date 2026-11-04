module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FreeYonedaSections

/-!
# The free abelian sheaf on a representable, in a coefficient universe of its own

Let `C` be a site with `C : Type u` and `Category.{v} C`. The free abelian sheaf on the
representable presheaf at `U : C`, and with it sheaf cohomology `H^p(U, -)`, are available in
Mathlib and in `DerivedSections/FreeYonedaSections.lean` only with the **coefficient universe
pinned to the universe of the homs of the site**: `Sheaf.cohomologyPresheafFunctor` is built from
`yoneda ⋙ (whiskeringRight _ _ _).obj AddCommGrpCat.free`, and `yoneda : C ⥤ Cᵒᵖ ⥤ Type v` forces
`AddCommGrpCat.free : Type v ⥤ AddCommGrpCat.{v}`, hence coefficients `AddCommGrpCat.{v}`.

That pinning is not avoidable by instance search, and it is the obstruction encountered in the
derived clause of [Stacks, Tag 0DCU]: there the site is `Opens X` for `X : TopCat.{u}`, so
`v = u`, while the coefficients the clause quantifies over are `AddCommGrpCat.{max (u + 1) v}`.
Writing one of those sheaves where the pinned theory wants its sheaf is a universe error, not a
reducibility failure:

```
Application type mismatch: J has type
  Sheaf.{u, max (u+1) v, u, max (u+2) (v+1)} (Opens.grothendieckTopology X.obj) AddCommGrpCat
but is expected to have type
  Sheaf.{u, u, u, u+1} (Opens.grothendieckTopology X.obj) AddCommGrpCat
```

This file removes the pinning, by replacing `yoneda` with Mathlib's
`CategoryTheory.uliftYoneda.{t} : C ⥤ Cᵒᵖ ⥤ Type (max t v)` throughout. The coefficient universe
becomes `max v t` with `t` free, so any coefficient universe dominating the homs of the site is
reachable; no `UnivLE` instance is involved, and at `t := v` the constructions are isomorphic to
the pinned ones by `freeYonedaIso` below, so nothing is weakened.

## Main definitions

All in the namespace `Stacks.Cohomology.FreeYonedaUnivLE`.

* `freeYoneda`: the free abelian sheaf on a representable, as a functor
  `C ⥤ Sheaf J AddCommGrpCat.{max v t}`.
* `sectionsEquiv`, `sectionsAddEquiv`: morphisms out of it are the sections, as a bijection and
  as an isomorphism of abelian groups.
* `gen`: its tautological section over `U`.
* `cohomologyPresheafFunctor`, `cohomologyPresheaf`: the cohomology presheaf of an abelian sheaf
  with coefficients in `max v t` and `Ext`-groups in a third universe `w'`, i.e.
  `Sheaf.cohomologyPresheafFunctor` with the coefficient universe freed.
* `extSectionsAddEquiv`: degree-zero `Ext` out of the free abelian sheaf on `U` is the group of
  sections over `U`.
* `freeYonedaIso`: at `t := v` this theory agrees, up to isomorphism, with the pinned one of
  `DerivedSections/FreeYonedaSections.lean`.

## Main results

* `cohomologyPresheafIsoSections`: degree-zero sheaf cohomology is the presheaf of sections, at
  independent universes.
* `sectionsEquiv_naturality`, `sectionsEquiv_naturality_left`, `sectionsEquiv_eq_app_gen` and
  their `Ext` counterparts: naturality of these identifications in the sheaf and in the
  representable.

## Implementation notes

The names repeat those of `DerivedSections/FreeYonedaSections.lean` in a namespace of their own
rather than shadowing them, because the two theories are both in scope in the files that compare
them; a file wanting the general one opens `Stacks.Cohomology.FreeYonedaUnivLE`.

`cohomologyPresheafIsoSections` is stated in a section specialising the `Ext` universe `w'` to the
coefficient universe `max v t`. It has to be: it is an isomorphism of `AddCommGrpCat.{w'}`-valued
presheaves with an `AddCommGrpCat.{max v t}`-valued one, so the two universes cannot differ there.
Everything above it is stated with `w'` free.

## References

* [Stacks Project, Tag 09V3](https://stacks.math.columbia.edu/tag/09V3)
* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Abelian

namespace Stacks.Cohomology.FreeYonedaUnivLE

universe w' t v u

noncomputable section

variable {C : Type u} [Category.{v} C]

section

variable (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{max v t}]

/-- **The free abelian sheaf on a representable presheaf of sets, in any coefficient universe
dominating the homs of the site.** This is `Stacks.Cohomology.FreeYoneda.freeYoneda` with
`yoneda` replaced by `uliftYoneda.{t}`, which is what frees the coefficients from
`AddCommGrpCat.{v}`. -/
abbrev freeYoneda : C ⥤ Sheaf J AddCommGrpCat.{max v t} :=
  uliftYoneda.{t} ⋙ (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.free ⋙ presheafToSheaf J _

end

variable {J : GrothendieckTopology C} [HasSheafify J AddCommGrpCat.{max v t}]

/-- Morphisms out of the free abelian sheaf on `U` are the sections over `U`. -/
def sectionsEquiv (U : C) (F : Sheaf J AddCommGrpCat.{max v t}) :
    ((freeYoneda.{t} J).obj U ⟶ F) ≃ ToType (F.obj.obj (op U)) :=
  ((sheafificationAdjunction J AddCommGrpCat.{max v t}).homEquiv _ _).trans
    (((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _).trans uliftYonedaEquiv.{t})

/-- `sectionsEquiv` as an isomorphism of abelian groups. -/
def sectionsAddEquiv (U : C) (F : Sheaf J AddCommGrpCat.{max v t}) :
    ((freeYoneda.{t} J).obj U ⟶ F) ≃+ ToType (F.obj.obj (op U)) where
  toEquiv := sectionsEquiv U F
  map_add' f g := by
    let q : ((((Functor.whiskeringRight Cᵒᵖ (Type max v t) AddCommGrpCat.{max v t}).obj
          AddCommGrpCat.free).obj (uliftYoneda.{t}.obj U)) ⟶
        (sheafToPresheaf J AddCommGrpCat.{max v t}).obj F) → ToType (F.obj.obj (op U)) := fun k ↦
      uliftYonedaEquiv.{t} ((AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv _ _ k)
    exact congrArg q ((sheafificationAdjunction J AddCommGrpCat.{max v t}).homAddEquiv_add _ _ f g)

/-- `sectionsAddEquiv U F` agrees with `sectionsEquiv U F` on every morphism. -/
theorem sectionsAddEquiv_apply (U : C) (F : Sheaf J AddCommGrpCat.{max v t})
    (α : (freeYoneda.{t} J).obj U ⟶ F) : sectionsAddEquiv U F α = sectionsEquiv U F α :=
  rfl

/-- The canonical section of the free abelian sheaf on `U` over `U` itself. -/
def gen (U : C) : ToType (((freeYoneda.{t} J).obj U).obj.obj (op U)) :=
  sectionsEquiv U ((freeYoneda.{t} J).obj U) (𝟙 _)

/-- `sectionsEquiv` is natural in the sheaf: composing with `β : F ⟶ G` corresponds to applying
`β` to sections over `U`. -/
theorem sectionsEquiv_naturality (U : C) {F G : Sheaf J AddCommGrpCat.{max v t}}
    (α : (freeYoneda.{t} J).obj U ⟶ F) (β : F ⟶ G) :
    sectionsEquiv U G (α ≫ β) = β.hom.app (op U) (sectionsEquiv U F α) := by
  dsimp only [sectionsEquiv, Equiv.trans_apply]
  rw [(sheafificationAdjunction J AddCommGrpCat.{max v t}).homEquiv_naturality_right]
  rfl

/-- The section corresponding to `α` is the image of the canonical section `gen U` under `α`. -/
theorem sectionsEquiv_eq_app_gen (U : C) (F : Sheaf J AddCommGrpCat.{max v t})
    (α : (freeYoneda.{t} J).obj U ⟶ F) :
    sectionsEquiv U F α = α.hom.app (op U) (gen.{t} U) :=
  (congrArg (sectionsEquiv U F) (Category.id_comp α).symm).trans
    (sectionsEquiv_naturality U (𝟙 _) α)

/-- `sectionsEquiv` is natural in the representable: precomposing with the map induced by
`h : V ⟶ U` corresponds to restricting sections along `h`. -/
theorem sectionsEquiv_naturality_left {U V : C} (h : V ⟶ U) (F : Sheaf J AddCommGrpCat.{max v t})
    (α : (freeYoneda.{t} J).obj U ⟶ F) :
    sectionsEquiv V F ((freeYoneda.{t} J).map h ≫ α) = F.obj.map h.op (sectionsEquiv U F α) := by
  dsimp only [sectionsEquiv, Equiv.trans_apply]
  rw [show (freeYoneda.{t} J).map h = (presheafToSheaf J AddCommGrpCat.{max v t}).map
      (((Functor.whiskeringRight Cᵒᵖ (Type max v t) AddCommGrpCat.{max v t}).obj
        AddCommGrpCat.free).map (uliftYoneda.{t}.map h)) from rfl,
    (sheafificationAdjunction J AddCommGrpCat.{max v t}).homEquiv_naturality_left,
    (AddCommGrpCat.adj.whiskerRight Cᵒᵖ).homEquiv_naturality_left]
  exact (uliftYonedaEquiv_naturality.{t} _ h.op).symm

section Ext

variable [HasExt.{w'} (Sheaf J AddCommGrpCat.{max v t})]

variable (J) in
/-- **The cohomology-presheaf bifunctor with the coefficient universe freed.** This is
`CategoryTheory.Sheaf.cohomologyPresheafFunctor` built on `freeYoneda` rather than on
`yoneda ⋙ AddCommGrpCat.free`, so that its coefficients are `AddCommGrpCat.{max v t}` instead of
`AddCommGrpCat.{v}`. -/
def cohomologyPresheafFunctor (n : ℕ) :
    Sheaf J AddCommGrpCat.{max v t} ⥤ Cᵒᵖ ⥤ AddCommGrpCat.{w'} :=
  Functor.flip (Functor.op (freeYoneda.{t} J) ⋙ extFunctor n)

/-- The presheaf `U ↦ H^n(U, F)`, with the coefficient universe freed. -/
abbrev cohomologyPresheaf (F : Sheaf J AddCommGrpCat.{max v t}) (n : ℕ) :
    Cᵒᵖ ⥤ AddCommGrpCat.{w'} :=
  (cohomologyPresheafFunctor.{w', t} J n).obj F

/-- Under `Ext.addEquiv₀`, composing a degree-zero `Ext` class with `Ext.mk₀ β` is
postcomposition with `β`. -/
theorem addEquiv₀_comp_mk₀ {A F G : Sheaf J AddCommGrpCat.{max v t}}
    (x : Ext.{w'} A F 0) (β : F ⟶ G) :
    Ext.addEquiv₀ (x.comp (Ext.mk₀ β) (add_zero 0)) = Ext.addEquiv₀ x ≫ β :=
  (Ext.mk₀_bijective A G).injective (by simp [← Ext.mk₀_comp_mk₀])

/-- Under `Ext.addEquiv₀`, composing `Ext.mk₀ α` with a degree-zero `Ext` class is
precomposition with `α`. -/
theorem addEquiv₀_mk₀_comp {A B F : Sheaf J AddCommGrpCat.{max v t}}
    (α : A ⟶ B) (x : Ext.{w'} B F 0) :
    Ext.addEquiv₀ ((Ext.mk₀ α).comp x (zero_add 0)) = α ≫ Ext.addEquiv₀ x :=
  (Ext.mk₀_bijective A F).injective (by simp [← Ext.mk₀_comp_mk₀])

/-- Degree-zero `Ext` out of the free abelian sheaf on `U` is the group of sections over `U`. -/
def extSectionsAddEquiv (U : C) (F : Sheaf J AddCommGrpCat.{max v t}) :
    Ext.{w'} ((freeYoneda.{t} J).obj U) F 0 ≃+ ToType (F.obj.obj (op U)) :=
  Ext.addEquiv₀.trans (sectionsAddEquiv U F)

/-- `extSectionsAddEquiv` is natural in the sheaf: composing with `Ext.mk₀ β` corresponds to
applying `β` to sections over `U`. -/
theorem extSectionsAddEquiv_naturality (U : C) {F G : Sheaf J AddCommGrpCat.{max v t}}
    (x : Ext.{w'} ((freeYoneda.{t} J).obj U) F 0) (β : F ⟶ G) :
    extSectionsAddEquiv U G (x.comp (Ext.mk₀ β) (add_zero 0)) =
      β.hom.app (op U) (extSectionsAddEquiv U F x) := by
  dsimp only [extSectionsAddEquiv, AddEquiv.trans_apply]
  rw [addEquiv₀_comp_mk₀]
  exact sectionsEquiv_naturality U _ β

/-- `extSectionsAddEquiv` is natural in the representable: precomposing with the class of the
map induced by `h : V ⟶ U` corresponds to restricting sections along `h`. -/
theorem extSectionsAddEquiv_naturality_left {U V : C} (h : V ⟶ U)
    (F : Sheaf J AddCommGrpCat.{max v t}) (x : Ext.{w'} ((freeYoneda.{t} J).obj U) F 0) :
    extSectionsAddEquiv V F ((Ext.mk₀ ((freeYoneda.{t} J).map h)).comp x (zero_add 0)) =
      F.obj.map h.op (extSectionsAddEquiv U F x) := by
  dsimp only [extSectionsAddEquiv, AddEquiv.trans_apply]
  rw [addEquiv₀_mk₀_comp]
  exact sectionsEquiv_naturality_left h F _

/-- The restriction maps of `cohomologyPresheaf` are precomposition with the induced map of free
abelian sheaves. -/
theorem cohomologyPresheaf_map_apply (F : Sheaf J AddCommGrpCat.{max v t}) (p : ℕ) {U V : C}
    (h : V ⟶ U) (x : Ext.{w'} ((freeYoneda.{t} J).obj U) F p) :
    (cohomologyPresheaf.{w', t} F p).map h.op x =
      (Ext.mk₀ ((freeYoneda.{t} J).map h)).comp x (zero_add p) :=
  rfl

/-- The action of `cohomologyPresheafFunctor` on a morphism of sheaves is postcomposition. -/
theorem cohomologyPresheafFunctor_map_app_apply {F G : Sheaf J AddCommGrpCat.{max v t}}
    (β : F ⟶ G) (p : ℕ) (U : C) (x : Ext.{w'} ((freeYoneda.{t} J).obj U) F p) :
    ((cohomologyPresheafFunctor.{w', t} J p).map β).app (op U) x =
      x.comp (Ext.mk₀ β) (add_zero p) :=
  rfl

end Ext

section DegreeZero

variable [HasExt.{max v t} (Sheaf J AddCommGrpCat.{max v t})]

/-- **Degree-zero sheaf cohomology is the presheaf of sections**, with the coefficient universe
freed. This is `Stacks.Cohomology.FreeYoneda.cohomologyPresheafIsoSections` with the coefficients
no longer pinned to the homs of the site. -/
def cohomologyPresheafIsoSections (F : Sheaf J AddCommGrpCat.{max v t}) :
    cohomologyPresheaf.{max v t, t} F 0 ≅ (sheafToPresheaf J AddCommGrpCat.{max v t}).obj F :=
  NatIso.ofComponents (fun U ↦ (extSectionsAddEquiv.{max v t} U.unop F).toAddCommGrpIso)
    (fun {_ _} h ↦ ConcreteCategory.hom_ext _ _ fun x ↦
      ((ConcreteCategory.comp_apply _ _ x).trans
        (extSectionsAddEquiv_naturality_left.{max v t} h.unop F x)).trans
        (ConcreteCategory.comp_apply _ _ x).symm)

/-- The component of `cohomologyPresheafIsoSections F` at `U` is `extSectionsAddEquiv U F`. -/
theorem cohomologyPresheafIsoSections_hom_app_apply (F : Sheaf J AddCommGrpCat.{max v t}) (U : C)
    (x : Ext.{max v t} ((freeYoneda.{t} J).obj U) F 0) :
    ((cohomologyPresheafIsoSections F).app (op U)).hom x =
      extSectionsAddEquiv.{max v t} U F x :=
  rfl

end DegreeZero

section Pinned

/-- **At `t := v` this theory is the pinned one.** The free abelian sheaf built on
`uliftYoneda.{v}` is isomorphic to the one built on `yoneda`, so no statement proved with the
freed coefficient universe is weaker than its pinned counterpart in
`DerivedSections/FreeYonedaSections.lean`. -/
def freeYonedaIso (J : GrothendieckTopology C) [HasSheafify J AddCommGrpCat.{v}] :
    freeYoneda.{v} J ≅ Stacks.Cohomology.FreeYoneda.freeYoneda J :=
  Functor.isoWhiskerRight uliftYonedaIsoYoneda.{v} _

end Pinned

end

end Stacks.Cohomology.FreeYonedaUnivLE

end
