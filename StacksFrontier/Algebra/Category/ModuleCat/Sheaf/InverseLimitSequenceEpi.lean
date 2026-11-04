module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ExactOnCoveringObjects
public import StacksFrontier.Algebra.Homology.DerivedCategory.InverseLimitComparisonHomBijective

/-!
# `lim M_n ⟶ ∏ M_n ⟶ ∏ M_n` for a tower of sheaves of modules

Let `(M_n)` be a tower of sheaves of modules on a site, and suppose that every object of the site
is covered by objects `U` over which every transition map `M_{n+1}(U) ⟶ M_n(U)` is surjective.
Then `lim M_n ⟶ ∏ M_n ⟶ ∏ M_n`, the second map being `1 - shift`, is short exact.  Over such a
`U` the sections of the sequence are the corresponding sequence of the tower of modules of
sections, since taking sections preserves limits, and `1 - shift` is surjective there; a map of
sheaves of modules surjective over enough objects is an epimorphism.

## Main results

* `Stacks.SheafOfModules.shortExact_inverseLimitSequence_of_surjective`: the statement above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u u' t


namespace Stacks.SheafOfModules

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{t}]

/-- **`lim M_n ⟶ ∏ M_n ⟶ ∏ M_n` is short exact for a tower of sheaves of modules whose transition
maps are surjective on sections over enough objects.** -/
theorem shortExact_inverseLimitSequence_of_surjective (P : ObjectProperty C)
    (hP : J.HasEnoughObjects P) (M : ℕᵒᵖ ⥤ SheafOfModules.{t} R)
    [HasProduct fun n : ℕ => M.obj ⟨n⟩] [HasLimit M]
    (hsurj : ∀ U : C, P U → ∀ n : ℕ,
      Function.Surjective ((M.map (homOfLE (Nat.le_succ n)).op).val.app (op U))) :
    (inverseLimitSequence M).ShortExact := by
  obtain ⟨hexact, hmono⟩ := inverseLimitSequence_exact_and_mono M
  refine { exact := hexact, mono_f := hmono, epi_g := ?_ }
  refine EpiMono.epi_of_surjective_of_hasEnoughObjects P hP _ fun U hU => ?_
  have : (SheafOfModules.evaluation R (op U)).Additive := ⟨rfl⟩
  have : PreservesLimitsOfShape (Discrete ℕ) (SheafOfModules.evaluation R (op U)) :=
    SheafOfModules.evaluationPreservesLimitsOfShape _ _ _
  have hiso : IsIso (piComparison (SheafOfModules.evaluation R (op U))
      (fun n : ℕ => M.obj ⟨n⟩)) := by
    rw [← PreservesProduct.iso_hom]
    infer_instance
  have hev := map_inverseLimitSequence_g M (SheafOfModules.evaluation R (op U))
  have h' : Epi (inverseLimitSequence (M ⋙ SheafOfModules.evaluation R (op U))).g :=
    (CategoryTheory.Limits.shortExact_inverseLimitSequence_of_surjective
      (M ⋙ SheafOfModules.evaluation R (op U))
      (hsurj U hU)).epi_g
  have hcomp : Epi ((SheafOfModules.evaluation R (op U)).map (inverseLimitSequence M).g ≫
      piComparison (SheafOfModules.evaluation R (op U)) (fun n : ℕ => M.obj ⟨n⟩)) := by
    rw [hev]
    exact @epi_comp _ _ _ _ _ _ (@IsIso.epi_of_iso _ _ _ _ _ hiso) _ h'
  have : Epi ((SheafOfModules.evaluation R (op U)).map (inverseLimitSequence M).g) :=
    (@epi_comp_iff_of_isIso _ _ _ _ _ _ _ hiso).1 hcomp
  exact (ModuleCat.epi_iff_surjective _).1 this

end Stacks.SheafOfModules

end
