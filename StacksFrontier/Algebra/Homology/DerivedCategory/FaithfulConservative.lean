module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import Mathlib.CategoryTheory.Abelian.Exact
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A faithful exact functor is conservative, on objects and on derived categories

A functor between abelian categories which is faithful and preserves zero morphisms reflects
isomorphisms; if it is moreover exact, it reflects isomorphisms of derived categories.

## Main results

* `Stacks.Cohomology.isIso_of_isIso_map_of_faithful`
* `Stacks.Cohomology.reflectsIsomorphisms_of_faithful`
* `Stacks.Cohomology.isIso_of_isIso_mapDerivedCategory_map_of_faithful`

## Implementation notes

`Dualizing.isIso_of_isIso_mapDerivedCategory_map` is the same statement for a FULLY faithful
functor, and that hypothesis is strictly stronger than the proof needs: fullness is used only at
the very last step, to reflect an isomorphism of homology objects.  Forgetting the module
structure of a sheaf of modules is faithful and exact but very far from full, so that version
does not apply to it, which is what this file is for.  The derived-category proof here is the
`Dualizing` one with its final `isIso_of_fully_faithful` replaced by the object-level lemma
below; everything before that step is unchanged.

Faithfulness alone suffices on objects because of
`CategoryTheory.Functor.reflects_exact_of_faithful`: a faithful functor reflects exactness of
short complexes, so it reflects monomorphisms (via the short complex `0 → X → Y`) and
epimorphisms (via `X → Y → 0`), and an abelian category is balanced.  Note how weak the
hypotheses of that Mathlib lemma are -- only `PreservesZeroMorphisms` and `Faithful` -- which is
why no exactness is needed for the object-level statement.

## References

* [Stacks Project, Tag 0D6J](https://stacks.math.columbia.edu/tag/0D6J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

namespace Stacks.Cohomology

/-- **A faithful functor preserving zero morphisms reflects isomorphisms between abelian
categories.**  It reflects monomorphisms and epimorphisms, by reflecting exactness of the two
short complexes `0 → X → Y` and `X → Y → 0`, and an abelian category is balanced. -/
@[sga "4 I 6.2" "(iii), special case"]
theorem isIso_of_isIso_map_of_faithful {C D : Type*} [Category C] [Abelian C] [Category D]
    [Abelian D] (F : C ⥤ D) [F.PreservesZeroMorphisms] [F.Faithful]
    {X Y : C} (f : X ⟶ Y) (hf : IsIso (F.map f)) : IsIso f := by
  have := hf
  have hm : Mono f := by
    have hS : ((ShortComplex.mk (0 : (0 : C) ⟶ X) f (by simp)).map F).Exact := by
      rw [ShortComplex.exact_iff_mono _ (by simp)]
      dsimp
      infer_instance
    have h := Functor.reflects_exact_of_faithful F _ hS
    rwa [ShortComplex.exact_iff_mono _ (by simp)] at h
  have he : Epi f := by
    have hS : ((ShortComplex.mk f (0 : Y ⟶ (0 : C)) (by simp)).map F).Exact := by
      rw [ShortComplex.exact_iff_epi _ (by simp)]
      dsimp
      infer_instance
    have h := Functor.reflects_exact_of_faithful F _ hS
    rwa [ShortComplex.exact_iff_epi _ (by simp)] at h
  exact isIso_of_mono_of_epi f

/-- The bundled form of `Stacks.Cohomology.isIso_of_isIso_map_of_faithful`, which is what the
Mathlib lemmas asking for `CategoryTheory.Functor.ReflectsIsomorphisms` consume -- among them
`HomologicalComplex.quasiIso_map_iff_of_preservesHomology`, that an exact functor reflects
quasi-isomorphisms of complexes.

Deliberately not an instance: its hypotheses hold for every forgetful functor between abelian
categories, so instance search would attempt it on every reflection goal in sight. -/
@[sga "4 I 6.2" "(iii), special case", sga "4 I 6.3" "a)"]
theorem reflectsIsomorphisms_of_faithful {C D : Type*} [Category C] [Abelian C] [Category D]
    [Abelian D] (F : C ⥤ D) [F.PreservesZeroMorphisms] [F.Faithful] :
    F.ReflectsIsomorphisms where
  reflects f hf := isIso_of_isIso_map_of_faithful F f hf

/-- **A faithful exact functor is conservative on derived categories:** a morphism of `D(C)`
whose image in `D(D)` is invertible is itself invertible.  An exact functor commutes with
cohomology degree by degree, and a faithful functor between abelian categories reflects
isomorphisms. -/
theorem isIso_of_isIso_mapDerivedCategory_map_of_faithful {C D : Type*} [Category C] [Abelian C]
    [HasDerivedCategory C] [Category D] [Abelian D] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.Faithful]
    {X Y : DerivedCategory C} (f : X ⟶ Y)
    (hf : IsIso (F.mapDerivedCategory.map f)) : IsIso f := by
  rw [DerivedCategory.isIso_iff]
  intro n
  have := hf
  have hnat :=
    (StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso F n).hom.naturality f
  have h₀ : IsIso ((F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor D n).map f) := by
    show IsIso ((DerivedCategory.homologyFunctor D n).map (F.mapDerivedCategory.map f))
    infer_instance
  have h₁ : IsIso
      ((StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso F n).hom.app X ≫
        (DerivedCategory.homologyFunctor C n ⋙ F).map f) := by
    rw [← hnat]
    infer_instance
  have h₂ : IsIso ((DerivedCategory.homologyFunctor C n ⋙ F).map f) :=
    IsIso.of_isIso_comp_left
      ((StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso F n).hom.app X) _
  have h₃ : IsIso (F.map ((DerivedCategory.homologyFunctor C n).map f)) := h₂
  exact isIso_of_isIso_map_of_faithful F _ h₃

end Stacks.Cohomology

end
