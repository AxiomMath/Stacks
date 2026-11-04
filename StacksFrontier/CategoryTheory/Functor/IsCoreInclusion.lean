module

public import Mathlib.CategoryTheory.Core

/-!
# Functors that present a category as the core of another

`CategoryTheory.Core.inclusion C : Core C ⥤ C` is the inclusion of the maximal subgroupoid of a
category.  This file defines the properties of a functor which characterise such an inclusion.

* `CategoryTheory.Functor.IsIsoWide`: `u` is faithful, every morphism of the source goes to an
  isomorphism, and every isomorphism between objects in the image is the image of a morphism.
  Equivalently, `u` identifies the source with a *wide* subcategory of the target whose morphisms
  are exactly the isomorphisms between the objects it reaches.
* `CategoryTheory.Functor.IsCoreInclusion`: iso-wide and essentially surjective, so that the
  source is the maximal subgroupoid of the whole target.

## Main definitions

* `CategoryTheory.Functor.IsIsoWide` and `CategoryTheory.Functor.IsCoreInclusion`.
* `CategoryTheory.Functor.IsCoreInclusion.toCore` and
  `CategoryTheory.Functor.IsCoreInclusion.coreEquivalence`: the comparison with
  `CategoryTheory.Core` of the target, and the statement that it is an equivalence.

## Main results

* `CategoryTheory.Core.isCoreInclusion_inclusion` and
  `CategoryTheory.Functor.isCoreInclusion_id`: the inclusion of a core, and the identity functor
  of a groupoid, are core inclusions.
* `CategoryTheory.Functor.isEquivalence_of_isCoreInclusion`: **an equivalence of categories
  restricts to an equivalence of cores**, in the following square form.  Given a commutative
  square of functors

  ```
  A' --w--> B'
  |u        |v
  A  --E--> B
  ```

  with `u` a core inclusion, `v` iso-wide and `E` an equivalence, the functor `w` is an
  equivalence.  Mathlib's `CategoryTheory.Equivalence.core` is the special case `u`, `v` the
  inclusions of `CategoryTheory.Core A` and `CategoryTheory.Core B`.
-/

@[expose] public section

namespace CategoryTheory

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {A : Type u₁} [Category.{v₁} A] {A' : Type u₂} [Category.{v₂} A']
  {B : Type u₃} [Category.{v₃} B] {B' : Type u₄} [Category.{v₄} B']

namespace Functor

/-- **`u : A' ⥤ A` presents `A'` as a wide subcategory of isomorphisms of `A`**: it is faithful,
every morphism of `A'` goes to an isomorphism of `A`, and every isomorphism of `A` between objects
in the image of `u` is the image of a morphism of `A'`. -/
structure IsIsoWide (u : A' ⥤ A) : Prop where
  /-- `u` is faithful. -/
  faithful : u.Faithful
  /-- Every morphism of `A'` goes to an isomorphism. -/
  isIso_map {X Y : A'} (g : X ⟶ Y) : IsIso (u.map g)
  /-- Every isomorphism between objects in the image is the image of a morphism. -/
  exists_map_eq {X Y : A'} (e : u.obj X ≅ u.obj Y) : ∃ g : X ⟶ Y, u.map g = e.hom

/-- **`u : A' ⥤ A` presents `A'` as the core of `A`**, i.e. as its maximal subgroupoid: `u` is
iso-wide and reaches every object of `A` up to isomorphism. -/
structure IsCoreInclusion (u : A' ⥤ A) : Prop extends IsIsoWide u where
  /-- `u` reaches every object of `A` up to isomorphism. -/
  essSurj : u.EssSurj

namespace IsIsoWide

variable {u : A' ⥤ A} (h : u.IsIsoWide)

include h

/-- An isomorphism between objects in the image of an iso-wide functor is the image of an
isomorphism. -/
lemma exists_iso_map_eq {X Y : A'} (e : u.obj X ≅ u.obj Y) :
    ∃ g : X ≅ Y, u.map g.hom = e.hom := by
  have := h.faithful
  obtain ⟨g, hg⟩ := h.exists_map_eq e
  obtain ⟨g', hg'⟩ := h.exists_map_eq e.symm
  refine ⟨⟨g, g', u.map_injective ?_, u.map_injective ?_⟩, hg⟩ <;>
    simp [hg, hg']

end IsIsoWide

/-- A functor `w` over an equivalence, between a core inclusion and an iso-wide functor, is an
equivalence. -/
private theorem isEquivalence_of_comm_core {u : A' ⥤ A} {v : B' ⥤ B} {w : A' ⥤ B'} {E : A ⥤ B}
    (hu : u.IsCoreInclusion) (hv : v.IsIsoWide) [E.IsEquivalence]
    (comm : w ⋙ v ≅ u ⋙ E) : w.IsEquivalence := by
  have := hu.faithful
  have := hv.faithful
  have : w.Faithful :=
    have : (w ⋙ v).Faithful := Faithful.of_iso comm.symm
    Faithful.of_comp (F := w) (G := v)
  have : w.Full := by
    refine ⟨fun {X Y} φ => ?_⟩
    obtain ⟨g, hg⟩ := hu.exists_map_eq
      (E.preimageIso ((comm.app X).symm ≪≫ @asIso _ _ _ _ _ (hv.isIso_map φ) ≪≫ comm.app Y))
    refine ⟨g, v.map_injective ?_⟩
    simpa [hg] using (Iso.eq_comp_inv (comm.app Y)).2 (comm.hom.naturality g)
  have : w.EssSurj := by
    refine ⟨fun Y' => ?_⟩
    obtain ⟨X, ⟨eX⟩⟩ := hu.essSurj.mem_essImage (E.objPreimage (v.obj Y'))
    obtain ⟨g, _⟩ := hv.exists_iso_map_eq
      ((comm.app X).trans ((E.mapIso eX).trans (E.objObjPreimageIso (v.obj Y'))))
    exact ⟨X, ⟨g⟩⟩
  exact { }

/-- The identity functor of a groupoid is a core inclusion: a groupoid is its own maximal
subgroupoid. -/
lemma isCoreInclusion_id (A : Type u₁) [Category.{v₁} A] [IsGroupoid A] :
    (𝟭 A).IsCoreInclusion where
  faithful := inferInstance
  isIso_map g := by simpa using inferInstanceAs (IsIso g)
  exists_map_eq e := ⟨e.hom, rfl⟩
  essSurj := inferInstance

end Functor

/-- **The inclusion of the core of a category is a core inclusion.** -/
lemma Core.isCoreInclusion_inclusion (A : Type u₁) [Category.{v₁} A] :
    (Core.inclusion A).IsCoreInclusion where
  faithful := inferInstance
  isIso_map g := g.iso.isIso_hom
  exists_map_eq e := ⟨.mk e, rfl⟩
  essSurj := ⟨fun Y => ⟨.mk Y, ⟨Iso.refl Y⟩⟩⟩

/-! ### The coherences of `CategoryTheory.Functor.coreCompInclusionIso` -/

/-- **The unit coherence of `CategoryTheory.Functor.coreCompInclusionIso`**: for `η : w ≅ 𝟭 A`,
the component of `w.coreCompInclusionIso.hom` at `X` followed by that of `η.hom` is the image of
`η.core.hom.app X` under `Core.inclusion A`. -/
lemma Core.inclusion_naturality_id (w : A ⥤ A) (η : w ≅ 𝟭 A) (X : Core A) :
    w.coreCompInclusionIso.hom.app X ≫ η.hom.app ((Core.inclusion A).obj X) =
      (Core.inclusion A).map (η.core.hom.app X) :=
  Category.id_comp _

/-- **The composition coherence of `CategoryTheory.Functor.coreCompInclusionIso`**: for
`η : w₁ ⋙ w₂ ≅ w`, the component of `w.coreCompInclusionIso.hom` at `X` followed by that of
`η.inv` is the image of `η.core.inv.app X` under `Core.inclusion A'`, followed by the components of
`w₂.coreCompInclusionIso.hom` and of `w₂.map` of `w₁.coreCompInclusionIso.hom`. -/
lemma Core.inclusion_naturality_comp (w₁ : A ⥤ B) (w₂ : B ⥤ A') (w : A ⥤ A')
    (η : w₁ ⋙ w₂ ≅ w) (X : Core A) :
    w.coreCompInclusionIso.hom.app X ≫ η.inv.app ((Core.inclusion A).obj X) =
      (Core.inclusion A').map (η.core.inv.app X) ≫
        w₂.coreCompInclusionIso.hom.app (w₁.core.obj X) ≫
          w₂.map (w₁.coreCompInclusionIso.hom.app X) :=
  (Category.id_comp (η.inv.app X.of)).trans
    ((Category.comp_id (η.inv.app X.of)).symm.trans
      (congrArg (fun z ↦ η.inv.app X.of ≫ z)
        (((Category.id_comp (w₂.map (𝟙 (w₁.obj X.of)))).trans (w₂.map_id _)).symm)))

namespace Functor.IsCoreInclusion

variable {u : A' ⥤ A} (h : u.IsCoreInclusion)

include h

/-- The comparison of the source of a core inclusion with the core of the target. -/
@[simps]
noncomputable def toCore : A' ⥤ Core A where
  obj X := .mk (u.obj X)
  map {_ _} g := .mk (@asIso _ _ _ _ _ (h.isIso_map g))
  map_id X := by ext; simp
  map_comp {_ _ _} g g' := by ext; simp

/-- The comparison functor `toCore` followed by the inclusion of the core is the core inclusion
`u`. -/
lemma toCore_comp_inclusion : h.toCore ⋙ Core.inclusion A = u := rfl

/-- **The comparison of the source of a core inclusion with the core of the target is an
equivalence.** -/
lemma isEquivalence_toCore : h.toCore.IsEquivalence :=
  isEquivalence_of_comm_core (E := 𝟭 A) h (Core.isCoreInclusion_inclusion A).toIsIsoWide
    (Iso.refl _)

/-- **The source of a core inclusion is equivalent to the core of the target.** -/
noncomputable def coreEquivalence : A' ≌ Core A :=
  have := h.isEquivalence_toCore
  h.toCore.asEquivalence

end Functor.IsCoreInclusion

namespace Functor

/-- **An equivalence of categories restricts to an equivalence of the wide subcategories of
isomorphisms.**  Given a square of functors commuting up to isomorphism

```
A' --w--> B'
|u        |v
A  --E--> B
```

in which `u` presents `A'` as the core of `A`, `v` presents `B'` as a wide subcategory of
isomorphisms of `B`, and `E` is an equivalence, the functor `w` is an equivalence. -/
theorem isEquivalence_of_isCoreInclusion {u : A' ⥤ A} {v : B' ⥤ B} {w : A' ⥤ B'} {E : A ⥤ B}
    (hu : u.IsCoreInclusion) (hv : v.IsIsoWide) [E.IsEquivalence]
    (comm : w ⋙ v ≅ u ⋙ E) : w.IsEquivalence :=
  isEquivalence_of_comm_core hu hv comm

end Functor

end CategoryTheory

end
