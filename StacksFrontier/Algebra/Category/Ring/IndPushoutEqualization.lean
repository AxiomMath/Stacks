module

public import StacksFrontier.Algebra.Category.Ring.IndPushoutFactorization

/-!
# Equalizing two elements of a base-changed colimit at a later stage

Let `R ⟶ M` be a ring map and let the `R`-algebra `Λ` be a filtered colimit of `R`-algebras drawn
from a family `P` — that is, `CategoryTheory.ObjectProperty.ind P Λ`. Let `D` be an `R`-algebra of
*finite presentation* with a map `D ⟶ Λ`. Two elements of `M ⊗[R] D` whose images in `M ⊗[R] Λ`
agree already agree in `M ⊗[R] D'` for a single stage `D'` of the colimit through which `D ⟶ Λ`
factors.

This is the companion of `CommRingCat.exists_factorization_of_ind_pushout`: that lemma descends a
*map* out of a finitely presented algebra to a stage, and this one descends an *equation* holding
at the colimit to a (possibly later) stage.

## Main results

* `CommRingCat.exists_stage_eq_of_ind_pushout`: **two elements of a base change of a finitely
  presented stage that agree over the colimit agree over a later stage**, together with the later
  stage's structure map to the colimit and the map from the given stage into it.

## Implementation notes

The two steps are: `D` is of finite presentation and `Λ` is the filtered colimit of the diagram,
so `D ⟶ Λ` factors through some `D_i` of the diagram compatibly with the structure maps
(`RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit`, as in
`CommRingCat.exists_factorization_of_ind_pushout`); and `M ⊗[R] Λ` is the filtered colimit of the
`M ⊗[R] D_j`, because base change `CategoryTheory.Under.pushout` is a left adjoint and
`CategoryTheory.Under.forget` and the forgetful functor to types preserve filtered colimits, so
two elements of `M ⊗[R] D_i` with the same image in it agree at a later `D_j`
(`CategoryTheory.Limits.Types.FilteredColimit.isColimit_eq_iff'`).

Note that the stage `D` of the hypothesis is *not* assumed to be one of the diagram's objects,
only to be finitely presented, which is what makes the lemma composable with
`CommRingCat.exists_factorization_of_ind_pushout`: the stage that lemma returns satisfies `P`, and
it is the property `P` — étaleness, in the application — that supplies finite presentation.

## References

* [Stacks Project, Tag 07C3](https://stacks.math.columbia.edu/tag/07C3)
* [Stacks Project, Tag 0DT9](https://stacks.math.columbia.edu/tag/0DT9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace CommRingCat

/-- **Two elements of the base change of a finitely presented stage which agree over a filtered
colimit already agree over a later stage.** If the `R`-algebra `Λ` is a filtered colimit of
`R`-algebras satisfying `P`, if `D` is an `R`-algebra of finite presentation with a map
`h : D ⟶ Λ`, and if two elements of `M ⊗[R] D` have the same image in `M ⊗[R] Λ`, then there is a
stage `D'` satisfying `P` with a map `φ : D ⟶ D'` over `Λ` for which the two images in `M ⊗[R] D'`
are already equal. -/
theorem exists_stage_eq_of_ind_pushout {R M : CommRingCat.{u}} (κ : R ⟶ M) {Λ : Under R}
    {P : ObjectProperty (Under R)} (hΛ : ObjectProperty.ind.{u} P Λ)
    {D : Under R} (hD : D.hom.hom.FinitePresentation) (h : D ⟶ Λ)
    (x y : ((Under.pushout κ).obj D).right)
    (hxy : ((Under.pushout κ).map h).right x = ((Under.pushout κ).map h).right y) :
    ∃ (D' : Under R), P D' ∧ ∃ (h' : D' ⟶ Λ) (φ : D ⟶ D'), φ ≫ h' = h ∧
      ((Under.pushout κ).map φ).right x = ((Under.pushout κ).map φ).right y := by
  obtain ⟨J, _, _, pres, hP⟩ := hΛ
  have : PreservesColimitsOfShape J (Under.pushout κ) :=
    (Under.mapPushoutAdj κ).leftAdjoint_preservesColimits.preservesColimitsOfShape
  obtain ⟨i, g', hg'₁, hg'₂⟩ :=
    RingHom.EssFiniteType.exists_eq_comp_ι_app_of_isColimit R (pres.diag ⋙ Under.forget R)
      { app := fun j => (pres.diag.obj j).hom
        naturality := fun j j' u => by
          simp only [Functor.const_obj_obj, Functor.const_obj_map, Functor.comp_map]
          exact (Under.w (pres.diag.map u)).symm }
      D.hom ((Under.forget R).mapCocone pres.cocone)
      (isColimitOfPreserves (Under.forget R) pres.isColimit) hD h.right
      (fun j => (Under.w h).trans (Under.w (pres.ι.app j)).symm)
  set φ₀ : D ⟶ pres.diag.obj i := Under.homMk g' hg'₁ with hφ₀def
  have hφ₀ : φ₀ ≫ pres.ι.app i = h := Under.UnderMorphism.ext hg'₂.symm
  have key : ∀ z : ((Under.pushout κ).obj D).right,
      ((Under.pushout κ).map (pres.ι.app i)).right (((Under.pushout κ).map φ₀).right z) =
        ((Under.pushout κ).map h).right z := by
    intro z
    rw [← hφ₀, Functor.map_comp]
    rfl
  obtain ⟨j, u, hu⟩ := (Types.FilteredColimit.isColimit_eq_iff'
      (isColimitOfPreserves (forget CommRingCat) (isColimitOfPreserves (Under.forget M)
        (isColimitOfPreserves (Under.pushout κ) pres.isColimit)))
      (((Under.pushout κ).map φ₀).right x) (((Under.pushout κ).map φ₀).right y)).mp
    (((key x).trans hxy).trans (key y).symm)
  refine ⟨pres.diag.obj j, hP j, pres.ι.app j, φ₀ ≫ pres.diag.map u, ?_, ?_⟩
  · rw [Category.assoc, pres.w u, hφ₀]
  · rw [Functor.map_comp]
    exact hu

end CommRingCat

end
