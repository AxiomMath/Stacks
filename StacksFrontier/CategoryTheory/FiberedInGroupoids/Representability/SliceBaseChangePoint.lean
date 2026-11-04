module

public import StacksFrontier.CategoryTheory.FiberedCategory.ElementsMap
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceBaseChangePresheaf

/-!
# The base change of a morphism of presheaves along a point, as a fibre product

Let `C` be a category, let `a : A ⟶ X` be a morphism of `C`, let `Hp` and `Gp` be presheaves of
sets on the slice `C/X` and let `α : Hp ⟶ Gp` be a morphism of presheaves. A *point of `El Gp`
with values in `A`* is a 1-morphism `σ : C/A ⥤ El Gp` over `C/X`, and the base change of
`El α : El Hp ⥤ El Gp` along it is represented by the presheaf
`CategoryTheory.PresheafOfCategories.twoFibreProductPresheaf` on `C/A`
(`CategoryTheory.PresheafOfCategories.nonempty_equivalenceOver_twoFibreProductPresheaf`).

`CategoryTheory.PresheafOfCategories.exists_isPullback_relocalize_twoFibreProductPresheaf`
identifies the relocalization of that presheaf with the fibre product `Hp ×_{Gp} h_{A → X}`,
but only once a *section* `β` of `Gp` over `A → X` restricting to the family of sections that
`σ` names is supplied. This file produces that section: a point with values in `A` names a
section over `A → X`, namely its value at the terminal object `A → A` of `C/A`, read through
the identification of `A → A → X` with `A → X`. Consequently

> **the structural morphism of the relocalization of the presheaf representing the base change
> of `α` along *any* point of `El Gp` with values in `A` is a base change of `α` itself.**

That is the step the proof of Stacks 045A needs for the presentation clause of an algebraic
stack: the base change of a presentation along an arbitrary scheme-valued point of the target is
a base change of the presentation read as a morphism of presheaves, so a property stable under
base change passes from one to the other.

## Main definitions

* `CategoryTheory.PresheafOfCategories.sectionOfPoint`: the section of `Gp` over `A → X` named by
  a point of `El Gp` with values in `A`.

## Main results

* `CategoryTheory.PresheafOfCategories.exists_section_sectionOfBasedFunctor_eq`: that section
  restricts, along the tautological morphisms, to the family of sections the point names — the
  hypothesis of
  `CategoryTheory.PresheafOfCategories.exists_isPullback_relocalize_twoFibreProductPresheaf`.
* `CategoryTheory.PresheafOfCategories.exists_isPullback_relocalize_of_point`: the relocalization
  of the representing presheaf of the base change along a point is the fibre product
  `Hp ×_{Gp} h_{A → X}`, for some section `β`.
* `CategoryTheory.PresheafOfCategories.natTransOfBasedFunctor_elementsMap`: the morphism of
  presheaves underlying `El α` is `α`.
* `CategoryTheory.OverShriek.relocalizePresheafFunctor_map_comp_relocalizeToYoneda`: the
  structural morphisms of relocalizations are compatible with a morphism of presheaves on the
  smaller slice.

## Implementation notes

The section is read off at the terminal object `A → A` of `C/A` and that is already all of it:
both the family a point names and the family of restrictions of a section are compatible with
restriction, so `CategoryTheory.PresheafOfCategories.sectionFamily_eq_of_eq_at_id` compares them
there. The comparison at that object is the identification
`(Over.map a).obj (A → A) = (A → X)`, whose underlying morphism of `C` is an identity, which is
why the tautological morphism of an arbitrary object `τ` composes with it to
`(Over.map a).map (τ ⟶ (A → A))`.

This is the converse of
`CategoryTheory.PresheafOfCategories.exists_pointOverMap_sectionOfBasedFunctor_eq`, which
produces a point from a section by 2-Yoneda. Here no fibred-in-groupoids hypothesis is needed
and nothing has to be transported: a point of a category of *elements* already names its
sections.

## References

* [Stacks Project, Tag 03YK](https://stacks.math.columbia.edu/tag/03YK)
* [Stacks Project, Tag 045A](https://stacks.math.columbia.edu/tag/045A)
* [Stacks Project, Tag 045B](https://stacks.math.columbia.edu/tag/045B)
-/

@[expose] public section

open CategoryTheory Opposite CategoryTheory.Limits CategoryTheory.OverShriek

namespace CategoryTheory

universe v u

namespace OverShriek

variable {C : Type u} [Category.{v} C] {X A : C} (a : A ⟶ X)

/-- **The structural morphisms of relocalizations are natural.** A morphism of presheaves on
`C/A` relocalizes to a morphism over the representable presheaf of `A → X`, because
relocalization does not change the factorization through `A` that a section carries. -/
theorem relocalizePresheafFunctor_map_comp_relocalizeToYoneda {F F' : (Over A)ᵒᵖ ⥤ Type v}
    (m : F ⟶ F') :
    (relocalizePresheafFunctor a).map m ≫ relocalizeToYoneda a F' = relocalizeToYoneda a F := by
  ext W x
  exact Over.OverMorphism.ext rfl

end OverShriek

namespace PresheafOfCategories

variable {C : Type u} [Category.{v} C] {X A : C} (a : A ⟶ X) {Hp Gp : (Over X)ᵒᵖ ⥤ Type v}

/-- The object `A → A → X` of `C/X` that the terminal object of `C/A` relocalizes to is the
object `A → X`. This is `CategoryTheory.Functor.overMap_obj_mkId` at the spelling `Over.mk a`,
which is the one this area of the library uses; it is restated rather than imported, since the
module carrying that lemma is otherwise unrelated. -/
theorem overMap_obj_mkId_eq_mk : (Over.map a).obj (Over.mk (𝟙 A)) = Over.mk a :=
  congrArg Over.mk (Category.id_comp a)

/-- The tautological morphism of an object `τ` of `C/A`, followed by the identification of
`A → A → X` with `A → X`, is the relocalization of the unique morphism from `τ` to the terminal
object of `C/A`: all three have the structure morphism of `τ` as underlying morphism of `C`. -/
theorem overMapTautHom_comp_eqToHom (τ : Over A) :
    overMapTautHom a τ ≫ eqToHom (overMap_obj_mkId_eq_mk a).symm =
      (Over.map a).map (Over.mkIdTerminal.from τ) :=
  Over.OverMorphism.ext (by simp)

variable (σ : Over A ⥤ (presheafOfCategories (Gp ⋙ typeToCat)).obj)
  (hσ : σ ⋙ discreteProjection Gp = Over.map a)

/-- **The section of `Gp` over `A → X` named by a point of `El Gp` with values in `A`**: the
element the point names at the terminal object `A → A` of `C/A`, read over `A → X` through the
identification `CategoryTheory.PresheafOfCategories.overMap_obj_mkId_eq_mk`. -/
def sectionOfPoint : Gp.obj (op (Over.mk a)) :=
  Gp.map (eqToHom (overMap_obj_mkId_eq_mk a).symm).op
    (sectionOfBasedFunctor σ hσ (Over.mk (𝟙 A)))

/-- **A point of `El Gp` with values in `A` comes from a section of `Gp` over `A → X`.** The
section `CategoryTheory.PresheafOfCategories.sectionOfPoint` restricts, along the tautological
morphisms, to the family of sections the point names; that is the hypothesis of
`CategoryTheory.PresheafOfCategories.exists_isPullback_relocalize_twoFibreProductPresheaf`.

Both families are compatible with restriction, so it is enough to compare them at the terminal
object `A → A` of `C/A`, where the comparison is the definition of the section. -/
theorem exists_section_sectionOfBasedFunctor_eq :
    ∃ β : yoneda.obj (Over.mk a) ⟶ Gp,
      ∀ τ : Over A, β.app (op ((Over.map a).obj τ)) (overMapTautHom a τ) =
        sectionOfBasedFunctor σ hσ τ := by
  refine ⟨yonedaEquiv.symm (sectionOfPoint a σ hσ), fun τ => ?_⟩
  have key :
      Gp.map (overMapTautHom a τ).op (sectionOfPoint a σ hσ) = sectionOfBasedFunctor σ hσ τ :=
    calc Gp.map (overMapTautHom a τ).op (sectionOfPoint a σ hσ)
        = Gp.map (overMapTautHom a τ ≫ eqToHom (overMap_obj_mkId_eq_mk a).symm).op
            (sectionOfBasedFunctor σ hσ (Over.mk (𝟙 A))) := by
          rw [op_comp, Gp.map_comp_apply]
          rfl
      _ = Gp.map ((Over.map a).map (Over.mkIdTerminal.from τ)).op
            (sectionOfBasedFunctor σ hσ (Over.mk (𝟙 A))) := by
          rw [overMapTautHom_comp_eqToHom]
      _ = sectionOfBasedFunctor σ hσ τ :=
          sectionOfBasedFunctor_map σ hσ (Over.mkIdTerminal.from τ)
  exact key

variable (θ : (presheafOfCategories (Hp ⋙ typeToCat)).obj ⥤
    (presheafOfCategories (Gp ⋙ typeToCat)).obj)
  (hθ : θ ⋙ discreteProjection Gp = discreteProjection Hp)

/-- **The relocalization of the presheaf representing the base change of a 1-morphism of
categories of elements along a point is a fibre product.** For any point `σ` of `El Gp` with
values in `A`, the relocalization along `a` of the presheaf representing the base change of
`θ : El Hp ⥤ El Gp` along `σ`, with its structural morphism
`CategoryTheory.OverShriek.relocalizeToYoneda`, is the fibre product of `Hp` and the
representable presheaf of `A → X` over `Gp`.

This removes the section hypothesis of
`CategoryTheory.PresheafOfCategories.exists_isPullback_relocalize_twoFibreProductPresheaf`: the
section is produced from the point by
`CategoryTheory.PresheafOfCategories.exists_section_sectionOfBasedFunctor_eq`. -/
theorem exists_isPullback_relocalize_of_point :
    ∃ (β : yoneda.obj (Over.mk a) ⟶ Gp)
      (c : (relocalizePresheafFunctor a).obj (twoFibreProductPresheaf σ hσ θ hθ) ⟶ Hp),
      IsPullback c (relocalizeToYoneda a (twoFibreProductPresheaf σ hσ θ hθ))
        (natTransOfBasedFunctor θ hθ) β := by
  obtain ⟨β, hβ⟩ := exists_section_sectionOfBasedFunctor_eq a σ hσ
  obtain ⟨c, hc⟩ := exists_isPullback_relocalize_twoFibreProductPresheaf a θ hθ σ hσ β hβ
  exact ⟨β, c, hc⟩

/-- The morphism of presheaves underlying the 1-morphism of categories of elements induced by a
morphism of presheaves is that morphism again. -/
theorem natTransOfBasedFunctor_elementsMap {F G : Cᵒᵖ ⥤ Type v} (m : F ⟶ G) :
    natTransOfBasedFunctor (elementsMap m) (elementsMap_comp_eq m) = m := by
  ext W x
  rfl

end PresheafOfCategories

end CategoryTheory

end
