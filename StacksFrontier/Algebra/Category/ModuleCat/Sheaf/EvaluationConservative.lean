module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono

/-!
# Sheaves of modules are detected by their modules of sections

A morphism of sheaves of modules on a site is a morphism of the underlying presheaves of
modules, and a morphism of presheaves of modules is its family of values on the objects of the
site. So although no single evaluation functor `M ↦ M(U)` is conservative, the family of all of
them is: a morphism of sheaves of modules whose value over every object is an isomorphism is an
isomorphism, and a sheaf of modules whose sections over every object vanish is a zero object.

Nothing here constrains the topology. The statements are about the forgetful functor to
presheaves of modules, which is faithful and reflects isomorphisms on any site.

## Main results

* `Stacks.SheafOfModulesEvaluation.hom_ext_of_forall_evaluation`: morphisms of sheaves of
  modules agreeing over every object of the site are equal.
* `Stacks.SheafOfModulesEvaluation.isIso_of_forall_isIso_evaluation`: **the evaluation functors
  are jointly conservative.**
* `Stacks.SheafOfModulesEvaluation.isZero_iff_forall_isZero_evaluation`: a sheaf of modules
  vanishes exactly when all of its modules of sections do.

## Implementation notes

Joint conservativity is proved through bijectivity of the components rather than by inverting
the morphism objectwise and checking naturality: `PresheafOfModules.mono_of_injective` and
`PresheafOfModules.epi_of_surjective` give a monomorphism and an epimorphism of presheaves of
modules, that category is abelian, and `SheafOfModules.forget` reflects isomorphisms.

## References

* [Stacks Project, Tag 03A4](https://stacks.math.columbia.edu/tag/03A4)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.SheafOfModulesEvaluation

universe u v m r

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (R : Sheaf J RingCat.{r})

/-- Evaluation of a sheaf of modules at an object of the site is additive, on any site: it is
the forgetful functor to presheaves of modules followed by evaluation of a presheaf of
modules, and both of those are additive. -/
instance evaluation_additive (U : Cᵒᵖ) : (SheafOfModules.evaluation.{m} R U).Additive :=
  inferInstanceAs
    (SheafOfModules.forget.{m} R ⋙ PresheafOfModules.evaluation R.obj U).Additive

/-- Two morphisms of sheaves of modules which agree after evaluation at every object of the
site are equal: a morphism of sheaves of modules is a morphism of the underlying presheaves of
modules, and those are given by their values on objects. -/
lemma hom_ext_of_forall_evaluation {M N : SheafOfModules.{m} R} {f g : M ⟶ N}
    (h : ∀ U : Cᵒᵖ, (SheafOfModules.evaluation.{m} R U).map f =
      (SheafOfModules.evaluation.{m} R U).map g) : f = g :=
  SheafOfModules.hom_ext (PresheafOfModules.hom_ext h)

/-- A sheaf of modules whose modules of sections all vanish is a zero object. The evaluation
functors are thus *jointly* conservative, even though no single one of them is. -/
lemma isZero_of_forall_isZero_evaluation {M : SheafOfModules.{m} R}
    (h : ∀ U : Cᵒᵖ, IsZero ((SheafOfModules.evaluation.{m} R U).obj M)) : IsZero M := by
  rw [IsZero.iff_id_eq_zero]
  refine hom_ext_of_forall_evaluation R fun U => ?_
  rw [CategoryTheory.Functor.map_id, Functor.map_zero]
  exact (h U).eq_of_src _ _

/-- A morphism of sheaves of modules all of whose evaluations are isomorphisms is itself an
isomorphism. The evaluation functors are thus *jointly* conservative, even though no single one
of them is. -/
lemma isIso_of_forall_isIso_evaluation {M N : SheafOfModules.{m} R} (f : M ⟶ N)
    (h : ∀ U : Cᵒᵖ, IsIso ((SheafOfModules.evaluation.{m} R U).map f)) : IsIso f := by
  have hb : ∀ U : Cᵒᵖ,
      Function.Bijective (((SheafOfModules.forget.{m} R).map f).app U) := fun U =>
    have := h U
    ConcreteCategory.bijective_of_isIso ((SheafOfModules.evaluation.{m} R U).map f)
  have : Mono ((SheafOfModules.forget.{m} R).map f) :=
    PresheafOfModules.mono_of_injective fun X => (hb X).1
  have : Epi ((SheafOfModules.forget.{m} R).map f) :=
    PresheafOfModules.epi_of_surjective fun X => (hb X).2
  have : IsIso ((SheafOfModules.forget.{m} R).map f) := isIso_of_mono_of_epi _
  exact isIso_of_reflects_iso f (SheafOfModules.forget.{m} R)

/-- A sheaf of modules is a zero object exactly when all of its modules of sections vanish. -/
lemma isZero_iff_forall_isZero_evaluation (M : SheafOfModules.{m} R) :
    IsZero M ↔ ∀ U : Cᵒᵖ, IsZero ((SheafOfModules.evaluation.{m} R U).obj M) := by
  refine ⟨fun h U => ?_, isZero_of_forall_isZero_evaluation R⟩
  rw [IsZero.iff_id_eq_zero, ← CategoryTheory.Functor.map_id, h.eq_of_src (𝟙 M) 0,
    Functor.map_zero]

end Stacks.SheafOfModulesEvaluation

end
