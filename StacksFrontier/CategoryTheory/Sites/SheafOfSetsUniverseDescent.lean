module

public import Mathlib.Basic.Countable.Small
public import Mathlib.CategoryTheory.ShrinkYoneda
public import StacksFrontier.CategoryTheory.Sites.SheafOfSetsUniverseLift

/-!
# Descending the universe of a finite locally constant sheaf of sets

`Stacks.ConstantSheaf.isFiniteLocallyConstant_sheafCompose_uliftFunctor` raises the universe of
the sections of a finite locally constant sheaf of sets on a site `C : Type u` with
`Category.{v} C`, from the smallest universe `max u v` in which such sheaves carry a Yoneda
lemma to any larger one `max u v s`. This file is the converse: a finite locally constant sheaf
of sets with sections in `Type (max u v s)` is the pointwise universe lift of one with sections
in `Type (max u v)`, and that one is again finite locally constant.

The content is that finite local constancy bounds the size of the sections. A sheaf is separated
for each of its covering sieves, so its sections over an object inject into the product of its
sections over the members of a trivializing covering family, and that family is indexed by a type
in `Type (max u v)` because that is the index universe of the covering families of
`Stacks.ConstantSheaf.IsFiniteLocallyConstant`. Over a member of the family the sheaf is the
constant sheaf on a finite type, and a finite type is the universe lift of a `max u v`-small one,
so — the universe lift commuting with the constant sheaf by
`CategoryTheory.constantCommuteCompose` — the sections there are a universe lift and hence
`max u v`-small. The sections over every object are therefore `max u v`-small, and
`CategoryTheory.FunctorToTypes.shrink` replaces them by a model in `Type (max u v)`.

## Main definitions

* `Stacks.Sheaves.UniverseLift.shrinkUliftIso`: the pointwise universe lift of the small model
  of a functor to types with small values is that functor.

## Main results

* `Stacks.Sheaves.UniverseLift.isSheaf_shrink`: the small model of a sheaf of sets whose
  sections are small is again a sheaf.
* `Stacks.ConstantSheaf.small_sections_of_isFiniteLocallyConstant`: the sections of a finite
  locally constant sheaf of sets over any object of the site are `max u v`-small, whatever the
  universe they are presented in.
* `Stacks.ConstantSheaf.exists_isFiniteLocallyConstant_uliftFunctor_iso`: a finite locally
  constant sheaf of sets with sections in `Type (max u v s)` is isomorphic to the pointwise
  universe lift of a finite locally constant sheaf of sets with sections in `Type (max u v)`.
* `Stacks.ConstantSheaf.isFiniteLocallyConstant_of_uliftFunctor_iso`: finite local constancy
  descends along such an isomorphism, the converse of
  `Stacks.ConstantSheaf.isFiniteLocallyConstant_sheafCompose_uliftFunctor`.

## Implementation notes

The small model is Mathlib's `CategoryTheory.FunctorToTypes.shrink`, and that it is again a
sheaf is `CategoryTheory.Presheaf.isSheaf_of_isSheaf_comp` for `CategoryTheory.uliftFunctor`,
which reflects limits of every size. The comparison isomorphism is written out rather than
obtained from `CategoryTheory.FunctorToTypes.shrinkCompUliftFunctorIso`, whose right-hand side
is the shrinking to the larger universe rather than the given functor.

Finite local constancy of the small model is read off the trivializations of the given sheaf by
full faithfulness of the universe lift on sheaves, `CategoryTheory.fullyFaithfulSheafCompose`
for `CategoryTheory.fullyFaithfulULiftFunctor`: the constant value `E` of a trivialization is
finite, hence `max u v`-small, hence the universe lift of `CategoryTheory.Shrink` of it, and the
universe lift carries the constant sheaf on that shrinking to the constant sheaf on `E`.

The universe lift is spelled `CategoryTheory.uliftFunctor.{s, max u v}` here, which is the shape
`CategoryTheory.GrothendieckTopology.hasSheafCompose_uliftFunctor` is stated at, so that sheaf
composition along it is available on the site itself and not only on its slices;
`Stacks.ConstantSheaf.isFiniteLocallyConstant_sheafCompose_uliftFunctor` spells the same functor
`CategoryTheory.uliftFunctor.{max u v s, max u v}`, which forces the lift level to be guessed
when the sheaf composition is needed on `C` rather than on a slice.

## References

* [Stacks Project, Tag 093Q](https://stacks.math.columbia.edu/tag/093Q)
* [Stacks Project, Tag 03RU](https://stacks.math.columbia.edu/tag/03RU)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe w s v u

namespace Stacks.Sheaves.UniverseLift

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- **The pointwise universe lift of the small model of a functor to types with small values is
that functor.** -/
def shrinkUliftIso (P : Cᵒᵖ ⥤ Type max u v s) [FunctorToTypes.Small.{max u v} P] :
    FunctorToTypes.shrink.{max u v} P ⋙ uliftFunctor.{s, max u v} ≅ P :=
  NatIso.ofComponents
    (fun X ↦ Equiv.toIso (Equiv.ulift.trans (equivShrink (P.obj X)).symm))
    (fun _ ↦ TypeCat.homEquiv.injective (funext fun _ ↦ Equiv.symm_apply_apply _ _))

/-- **A section of a sheaf of sets is determined by its restrictions along a covering family.**
A sheaf is separated for the sieve generated by the family, and every arrow of that sieve
factors through a member of it. -/
theorem injective_restrict_ofArrows (F : Sheaf J (Type w)) {U : C} {I : Type*}
    (X : I → C) (f : ∀ i, X i ⟶ U) (hf : Sieve.ofArrows X f ∈ J U) :
    Function.Injective (fun x : F.obj.obj (op U) ↦ fun i ↦ F.obj.map (f i).op x) := by
  intro x y hxy
  refine (((isSheaf_iff_isSheaf_of_type J F.obj).1 F.property).isSeparated
    (Sieve.ofArrows X f) hf).ext ?_
  rintro Y g ⟨W, a, b, ⟨i⟩, rfl⟩
  simp only [op_comp, Functor.map_comp_apply]
  exact congrArg _ (congrFun hxy i)

/-- **The small model of a sheaf of sets with small sections is again a sheaf.** Its pointwise
universe lift is isomorphic to the given sheaf, and the universe lift reflects limits. -/
theorem isSheaf_shrink (P : Cᵒᵖ ⥤ Type max u v s) [FunctorToTypes.Small.{max u v} P]
    (hP : Presheaf.IsSheaf J P) :
    Presheaf.IsSheaf J (FunctorToTypes.shrink.{max u v} P) :=
  Presheaf.isSheaf_of_isSheaf_comp J _ uliftFunctor.{s, max u v}
    ((Presheaf.isSheaf_of_iso_iff (shrinkUliftIso.{s, v, u} P)).2 hP)

end Stacks.Sheaves.UniverseLift

namespace Stacks.ConstantSheaf

open Stacks.Sheaves.UniverseLift

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- The universe lift of the constant sheaf on the small model of a finite type `E` is the
constant sheaf on `E`. -/
private def constantSheaf_uliftFunctor_shrink_iso [HasWeakSheafify J (Type max u v)]
    [HasWeakSheafify J (Type max u v s)] (E : Type max u v s) [Small.{max u v} E] :
    (sheafCompose J uliftFunctor.{s, max u v}).obj
        ((constantSheaf J (Type max u v)).obj (Shrink.{max u v} E)) ≅
      (constantSheaf J (Type max u v s)).obj E :=
  (constantCommuteCompose J uliftFunctor.{s, max u v}).app (Shrink.{max u v} E) ≪≫
    (constantSheaf J (Type max u v s)).mapIso
      (Equiv.toIso (Equiv.ulift.trans (equivShrink E).symm))

/-- **The sections of the constant sheaf of sets on a finite type are small.** A finite type is
the universe lift of a `max u v`-small type, and the universe lift commutes with the constant
sheaf, so the sections are a universe lift. -/
theorem small_constantSheaf_sections [HasWeakSheafify J (Type max u v)]
    [HasWeakSheafify J (Type max u v s)] (E : Type max u v s) [Finite E] (Y : C) :
    Small.{max u v} (((constantSheaf J (Type max u v s)).obj E).obj.obj (op Y)) := by
  have : Small.{max u v} E := inferInstance
  let k : ((constantSheaf J (Type max u v s)).obj E).obj.obj (op Y) ≅
      (((constantSheaf J (Type max u v)).obj (Shrink.{max u v} E)).obj ⋙
        uliftFunctor.{s, max u v}).obj (op Y) :=
    ((sheafSections J (Type max u v s)).obj (op Y)).mapIso
      (constantSheaf_uliftFunctor_shrink_iso J E).symm
  exact small_map (k.toEquiv.trans Equiv.ulift)

/-- **The sections of a finite locally constant sheaf of sets are small.** They inject into the
product, over a trivializing covering family of the object, of the sections over its members,
and those are the sections of a constant sheaf on a finite type. -/
theorem small_sections_of_isFiniteLocallyConstant
    [∀ V : C, HasWeakSheafify (J.over V) (Type max u v)]
    [∀ V : C, HasWeakSheafify (J.over V) (Type max u v s)]
    (F : Sheaf J (Type max u v s)) (hF : IsFiniteLocallyConstant J F) (U : C) :
    Small.{max u v} (F.obj.obj (op U)) := by
  obtain ⟨I, X, f, hf, h⟩ := hF.exists_finite_cover U
  have hi : ∀ i, Small.{max u v} (F.obj.obj (op (X i))) := by
    intro i
    obtain ⟨E, _, ⟨e⟩⟩ := h i
    exact small_map (hβ := small_constantSheaf_sections.{s, v, max u v} (J.over (X i)) E
      (Over.mk (𝟙 (X i)))) (((sheafSections (J.over (X i)) (Type max u v s)).obj
      (op (Over.mk (𝟙 (X i))))).mapIso e).symm.toEquiv
  exact small_of_injective (injective_restrict_ofArrows J F X f hf)

/-- **Finite local constancy descends along the pointwise universe lift of a sheaf of sets.**
This is the converse of
`Stacks.ConstantSheaf.isFiniteLocallyConstant_sheafCompose_uliftFunctor`. -/
theorem isFiniteLocallyConstant_of_uliftFunctor_iso
    [∀ V : C, HasWeakSheafify (J.over V) (Type max u v)]
    [∀ V : C, HasWeakSheafify (J.over V) (Type max u v s)]
    {F₀ : Sheaf J (Type max u v)} {F : Sheaf J (Type max u v s)}
    (e : (sheafCompose J uliftFunctor.{s, max u v}).obj F₀ ≅ F)
    (hF : IsFiniteLocallyConstant J F) : IsFiniteLocallyConstant J F₀ := by
  refine ⟨fun U ↦ ?_⟩
  obtain ⟨I, X, f, hf, h⟩ := hF.exists_finite_cover U
  refine ⟨I, X, f, hf, fun i ↦ ?_⟩
  obtain ⟨E, _, ⟨eE⟩⟩ := h i
  have : Small.{max u v} E := inferInstance
  refine ⟨Shrink.{max u v} E, .of_equiv E (equivShrink E), ⟨?_⟩⟩
  exact (fullyFaithfulSheafCompose (J.over (X i))
    fullyFaithfulULiftFunctor.{s, max u v}).preimageIso
    (constantSheaf_uliftFunctor_shrink_iso (J.over (X i)) E ≪≫ eE ≪≫
      (J.overPullback (Type max u v s) (X i)).mapIso e.symm)

/-- **A finite locally constant sheaf of sets is the pointwise universe lift of a finite locally
constant sheaf of sets with sections in the smallest universe.** -/
theorem exists_isFiniteLocallyConstant_uliftFunctor_iso
    [∀ V : C, HasWeakSheafify (J.over V) (Type max u v)]
    [∀ V : C, HasWeakSheafify (J.over V) (Type max u v s)]
    (F : Sheaf J (Type max u v s)) (hF : IsFiniteLocallyConstant J F) :
    ∃ F₀ : Sheaf J (Type max u v), IsFiniteLocallyConstant J F₀ ∧
      Nonempty ((sheafCompose J uliftFunctor.{s, max u v}).obj F₀ ≅ F) := by
  have : FunctorToTypes.Small.{max u v, max u v s, v, u} F.obj := fun X ↦
    small_sections_of_isFiniteLocallyConstant.{s, v, u} J F hF X.unop
  let F₀ : Sheaf J (Type max u v) :=
    ⟨FunctorToTypes.shrink.{max u v} F.obj, isSheaf_shrink.{s, v, u} J F.obj F.property⟩
  have e : (sheafCompose J uliftFunctor.{s, max u v}).obj F₀ ≅ F :=
    (fullyFaithfulSheafToPresheaf J (Type max u v s)).preimageIso
      (shrinkUliftIso.{s, v, u} F.obj)
  exact ⟨F₀, isFiniteLocallyConstant_of_uliftFunctor_iso J e hF, ⟨e⟩⟩

end Stacks.ConstantSheaf

end
