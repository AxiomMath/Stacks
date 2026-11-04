module

public import Mathlib.CategoryTheory.Limits.Final.Type
public import StacksFrontier.CategoryTheory.Sites.GlobalSections

/-!
# Global sections only see the index category up to equivalence

The global sections `Γ(C, F) = Mor_{PSh(C)}(*, F)` of Stacks 06UN
(`CategoryTheory.Presheaf.globalSections`) are the compatible families of sections of `F`,
and a compatible family is determined by its values on a part of the index category that is
large enough. This file records the two consequences of that which the equalizer presentation
of equation 075M needs:

* precomposing `F` with a functor `u : C ⥤ D` whose opposite is initial does not change the
  global sections (`CategoryTheory.Presheaf.globalSectionsPrecompEquivOfInitial`), and
* in particular precomposing with an *equivalence* does not
  (`CategoryTheory.Presheaf.globalSectionsPrecompEquiv`).

Both come from `CategoryTheory.Functor.bijective_sectionsPrecomp`, which says exactly that
restriction of compatible families along an initial functor is bijective, read through the
identification `CategoryTheory.Presheaf.globalSectionsEquivSections` of global sections with
compatible families.

## Main definitions

* `CategoryTheory.Presheaf.globalSectionsPrecompEquivOfInitial`: the bijection
  `Γ(D, F) ≃ Γ(C, u^{op} ⋙ F)` for `u.op` initial.
* `CategoryTheory.Presheaf.globalSectionsPrecompEquiv`: its specialization to an equivalence
  `e : C ≌ D`, i.e. **invariance of global sections under an equivalence of the index
  category**.

## Main results

* `CategoryTheory.Presheaf.globalSectionsEquivSections_globalSectionsPrecompEquivOfInitial`
  and `CategoryTheory.Presheaf.globalSectionsEquivSections_globalSectionsPrecompEquiv`: the
  bijections are computed on sections — the family attached to the transported global section
  has, at an object `X` of `C`, the value the original family has at `u X`. This is what makes
  the bijections usable: an identification of global sections which one cannot evaluate says
  nothing about any individual section.
* `CategoryTheory.Presheaf.globalSectionsPrecompEquiv_naturality`: the bijection for an
  equivalence is natural in the presheaf.

## References

* [Stacks Project, Tag 06UN](https://stacks.math.columbia.edu/tag/06UN)
-/

@[expose] public section

namespace CategoryTheory.Presheaf

open Limits Opposite

universe w v₁ v₂ u₁ u₂

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- Restriction of compatible families of sections along a functor whose opposite is initial is
a bijection: this is `CategoryTheory.Functor.bijective_sectionsPrecomp` read on global sections
in the sense of Stacks 06UN. -/
noncomputable def globalSectionsPrecompEquivOfInitial (u : C ⥤ D) [u.op.Initial]
    (F : Dᵒᵖ ⥤ Type w) :
    globalSections F ≃ globalSections (u.op ⋙ F) :=
  (globalSectionsEquivSections F).trans
    ((Equiv.ofBijective _ (Functor.bijective_sectionsPrecomp u.op F)).trans
      (globalSectionsEquivSections (u.op ⋙ F)).symm)

/-- The bijection `globalSectionsPrecompEquivOfInitial` on sections: the compatible family of
the transported global section has at `X` the value the original family has at `u X`. -/
theorem globalSectionsEquivSections_globalSectionsPrecompEquivOfInitial (u : C ⥤ D)
    [u.op.Initial] (F : Dᵒᵖ ⥤ Type w) (s : globalSections F) (X : C) :
    (globalSectionsEquivSections (u.op ⋙ F)
        (globalSectionsPrecompEquivOfInitial u F s)).1 (op X) =
      (globalSectionsEquivSections F s).1 (op (u.obj X)) := by
  simp only [globalSectionsPrecompEquivOfInitial, Equiv.trans_apply,
    Equiv.apply_symm_apply, Equiv.ofBijective_apply, Functor.sectionsPrecomp_coe,
    Functor.op_obj]

/-- **Invariance of global sections under an equivalence of the index category.** For an
equivalence `e : C ≌ D` the global sections of a presheaf on `D` are the global sections of its
restriction along `e`.

A global section of `F` is a compatible family of sections of `F`, and `e` matches the objects
and morphisms of `C` with those of `D` up to isomorphism, so the two kinds of family determine
each other. Formally the opposite of an equivalence is an initial functor, and this is
`globalSectionsPrecompEquivOfInitial` at it. -/
noncomputable def globalSectionsPrecompEquiv (e : C ≌ D) (F : Dᵒᵖ ⥤ Type w) :
    globalSections F ≃ globalSections (e.functor.op ⋙ F) :=
  globalSectionsPrecompEquivOfInitial e.functor F

/-- The bijection `globalSectionsPrecompEquiv` on sections. -/
theorem globalSectionsEquivSections_globalSectionsPrecompEquiv (e : C ≌ D) (F : Dᵒᵖ ⥤ Type w)
    (s : globalSections F) (X : C) :
    (globalSectionsEquivSections (e.functor.op ⋙ F)
        (globalSectionsPrecompEquiv e F s)).1 (op X) =
      (globalSectionsEquivSections F s).1 (op (e.functor.obj X)) :=
  globalSectionsEquivSections_globalSectionsPrecompEquivOfInitial e.functor F s X

/-- A global section of `F` read as a compatible family, pushed along a homomorphism `η` of
presheaves, is the original family with `η` applied at each object. -/
theorem globalSectionsEquivSections_comp {F H : Cᵒᵖ ⥤ Type w} (s : globalSections F)
    (η : F ⟶ H) (X : Cᵒᵖ) :
    (globalSectionsEquivSections H (s ≫ η)).1 X =
      η.app X ((globalSectionsEquivSections F s).1 X) :=
  rfl

/-- `globalSectionsPrecompEquivOfInitial` is natural in the presheaf. -/
theorem globalSectionsPrecompEquivOfInitial_naturality (u : C ⥤ D) [u.op.Initial]
    {F H : Dᵒᵖ ⥤ Type w} (η : F ⟶ H) (s : globalSections F) :
    globalSectionsPrecompEquivOfInitial u H (s ≫ η) =
      globalSectionsPrecompEquivOfInitial u F s ≫ Functor.whiskerLeft u.op η := by
  apply (globalSectionsEquivSections (u.op ⋙ H)).injective
  apply Subtype.ext
  funext X
  obtain ⟨X, rfl⟩ : ∃ Y : C, op Y = X := ⟨X.unop, rfl⟩
  rw [globalSectionsEquivSections_globalSectionsPrecompEquivOfInitial u H (s ≫ η) X,
    globalSectionsEquivSections_comp (globalSectionsPrecompEquivOfInitial u F s)
      (Functor.whiskerLeft u.op η) (op X),
    globalSectionsEquivSections_globalSectionsPrecompEquivOfInitial u F s X,
    globalSectionsEquivSections_comp s η (op (u.obj X))]
  rfl

/-- `globalSectionsPrecompEquiv` is natural in the presheaf. -/
theorem globalSectionsPrecompEquiv_naturality (e : C ≌ D) {F H : Dᵒᵖ ⥤ Type w} (η : F ⟶ H)
    (s : globalSections F) :
    globalSectionsPrecompEquiv e H (s ≫ η) =
      globalSectionsPrecompEquiv e F s ≫ Functor.whiskerLeft e.functor.op η :=
  globalSectionsPrecompEquivOfInitial_naturality e.functor η s

end CategoryTheory.Presheaf
