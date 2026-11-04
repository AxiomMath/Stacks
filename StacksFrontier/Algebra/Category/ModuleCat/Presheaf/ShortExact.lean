module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact

/-!
# Short exactness of presheaves of modules is objectwise

The category of presheaves of modules over a presheaf of rings is abelian with its kernels,
cokernels and homology formed objectwise, so a presheaf of modules is zero, and a short complex
of presheaves of modules is short exact, as soon as this holds at every object of the site.

## Main results

* `PresheafOfModules.isZero_iff_forall_isZero_obj` — a presheaf of modules is a zero object
  exactly when all its modules of sections are.
* `PresheafOfModules.shortExact_of_objectwise` — a short complex of presheaves of modules is
  short exact as soon as it is short exact at every object of the site.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w w' v₁ u₁

namespace PresheafOfModules

variable {E : Type u₁} [Category.{v₁} E] {R : Eᵒᵖ ⥤ RingCat.{w'}}

/-- A presheaf of modules is a zero object exactly when all its modules of sections are. -/
theorem isZero_iff_forall_isZero_obj (M : PresheafOfModules.{w} R) :
    IsZero M ↔ ∀ X, IsZero (M.obj X) := by
  rw [IsZero.iff_id_eq_zero]
  refine ⟨fun h X => ?_, fun h => PresheafOfModules.hom_ext fun X => ?_⟩
  · exact (IsZero.iff_id_eq_zero _).2 (by simpa using congrArg (fun m : M ⟶ M => m.app X) h)
  · rw [PresheafOfModules.zero_app, PresheafOfModules.id_app]
    exact (IsZero.iff_id_eq_zero (M.obj X)).1 (h X)

/-- A short complex of presheaves of modules is short exact as soon as it is short exact at
every object of the site. -/
theorem shortExact_of_objectwise (S : ShortComplex (PresheafOfModules.{w} R))
    (h : ∀ X, (S.map (evaluation R X)).ShortExact) : S.ShortExact where
  exact := by
    rw [ShortComplex.exact_iff_isZero_homology, isZero_iff_forall_isZero_obj]
    intro X
    exact (S.mapHomologyIso (evaluation R X)).isZero_iff.mp
      ((ShortComplex.exact_iff_isZero_homology _).mp (h X).exact)
  mono_f := PresheafOfModules.mono_of_injective (f := S.f) fun {X} =>
    (ModuleCat.mono_iff_injective _).1 (h X).mono_f
  epi_g := PresheafOfModules.epi_of_surjective (f := S.g) fun {X} =>
    (ModuleCat.epi_iff_surjective _).1 (h X).epi_g

end PresheafOfModules

end
