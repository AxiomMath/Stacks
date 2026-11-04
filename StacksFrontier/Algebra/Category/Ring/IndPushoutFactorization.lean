module

public import Mathlib.Algebra.Category.Ring.Colimits
public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.CategoryTheory.Comma.Over.Pullback
public import Mathlib.CategoryTheory.Limits.Preserves.Over
public import Mathlib.CategoryTheory.ObjectProperty.Ind

/-!
# Factoring a map out of a finitely presented algebra through a stage of a base-changed colimit

Let `R ⟶ A` be a ring map and let the `R`-algebra `Λ` be a filtered colimit of `R`-algebras
drawn from a family `P` — that is, `CategoryTheory.ObjectProperty.ind P Λ`. Then the
`A`-algebra `A ⊗[R] Λ` is the filtered colimit of the `A`-algebras `A ⊗[R] D` as `D` runs over
the stages, because base change `CategoryTheory.Under.pushout` is a left adjoint and therefore
preserves the colimit. Consequently an `A`-algebra map out of an `A`-algebra of *finite
presentation* into `A ⊗[R] Λ` factors through `A ⊗[R] D` for a single stage `D`, compatibly
with the structure map `D ⟶ Λ` of that stage.

## Main results

* `CommRingCat.exists_factorization_of_ind_pushout`: **the factorization through a single
  stage**, together with the stage's structure map to the colimit.

## Implementation notes

The conclusion keeps the stage's structure map `h : D ⟶ Λ` and asserts the factorization through
its base change `(Under.pushout ι).map h`, not merely through some map
`(Under.pushout ι).obj D ⟶ (Under.pushout ι).obj Λ`. For this reason the statement is not
derived from `CommRingCat.ind_under_iff_exists_factorization` (Tag 07C3), whose object property
on `Under A` cannot mention `Λ`.

## References

* [Stacks Project, Tag 07C3](https://stacks.math.columbia.edu/tag/07C3)
* [Stacks Project, Tag 05N9](https://stacks.math.columbia.edu/tag/05N9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CommRingCat

/-- **An `A`-algebra map of finite presentation into a base-changed filtered colimit factors
through a single stage.** If the `R`-algebra `Λ` is a filtered colimit of `R`-algebras satisfying
`P`, and `X` is an `A`-algebra of finite presentation, then every `A`-algebra map
`X ⟶ A ⊗[R] Λ` factors as `X ⟶ A ⊗[R] D ⟶ A ⊗[R] Λ` for a stage `D` satisfying `P`, the second
map being the base change of the structure map `D ⟶ Λ`. -/
theorem exists_factorization_of_ind_pushout {R A : CommRingCat.{u}} (ι : R ⟶ A) {Λ : Under R}
    {P : ObjectProperty (Under R)} (hΛ : ObjectProperty.ind.{u} P Λ)
    {X : Under A} (hX : X.hom.hom.FinitePresentation)
    (f : X ⟶ (Under.pushout ι).obj Λ) :
    ∃ (D : Under R), P D ∧ ∃ (h : D ⟶ Λ) (g : X ⟶ (Under.pushout ι).obj D),
      g ≫ (Under.pushout ι).map h = f := by
  obtain ⟨J, _, _, pres, hP⟩ := hΛ
  have : PreservesColimitsOfShape J (Under.pushout ι) :=
    (Under.mapPushoutAdj ι).leftAdjoint_preservesColimits.preservesColimitsOfShape
  obtain ⟨i, g', hg'₁, hg'₂⟩ :=
    RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit A
      (pres.diag ⋙ Under.pushout ι ⋙ Under.forget A)
      { app := fun j => ((Under.pushout ι).obj (pres.diag.obj j)).hom
        naturality := fun j j' u => by
          simp only [Functor.const_obj_obj, Functor.const_obj_map, Functor.comp_map]
          exact (Under.w ((Under.pushout ι).map (pres.diag.map u))).symm }
      X.hom ((Under.forget A).mapCocone ((Under.pushout ι).mapCocone pres.cocone))
      (isColimitOfPreserves (Under.forget A)
        (isColimitOfPreserves (Under.pushout ι) pres.isColimit)) hX f.right
      (fun j => (Under.w f).trans (Under.w ((Under.pushout ι).map (pres.ι.app j))).symm)
  exact ⟨pres.diag.obj i, hP i, pres.ι.app i, Under.homMk g' hg'₁,
    Under.UnderMorphism.ext hg'₂.symm⟩

end CommRingCat

end
