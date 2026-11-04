module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.Adjunction.Limits

/-!
# A fully faithful left adjoint and limits landing in its essential image

Let `L ⊣ R` with `L` fully faithful, so that the unit is an isomorphism. For a diagram `F` in the
source, the transpose of the comparison `L (lim F) ⟶ lim (F ⋙ L)` is the composite of
`lim F ≅ lim (F ⋙ L ⋙ R)`, induced by the unit, with the comparison
`lim (F ⋙ L ⋙ R) ≅ R (lim (F ⋙ L))`, which is invertible when `R` preserves the limit. The
comparison itself is that transpose followed by the counit at `lim (F ⋙ L)`, which is invertible
exactly when `lim (F ⋙ L)` lies in the essential image of `L`.

## Main results

* `CategoryTheory.Adjunction.isIso_limit_post_of_mem_essImage`: `L` preserves the limit of `F`
  when the limit of `F ⋙ L` lies in its essential image.
-/

@[expose] public section

namespace CategoryTheory

open Limits

variable {C D J : Type*} [Category C] [Category D] [Category J] {L : C ⥤ D} {R : D ⥤ C}

/-- **A fully faithful left adjoint commutes with a limit landing in its essential image.** Let
`L ⊣ R` with `L` fully faithful, and let `F : J ⥤ C` have a limit such that `F ⋙ L` has a limit
preserved by `R`. If `lim (F ⋙ L)` lies in the essential image of `L`, the comparison
`L (lim F) ⟶ lim (F ⋙ L)` is an isomorphism. -/
theorem Adjunction.isIso_limit_post_of_mem_essImage (adj : L ⊣ R) [L.Full] [L.Faithful]
    (F : J ⥤ C) [HasLimit F] [HasLimit (F ⋙ L)] [PreservesLimit (F ⋙ L) R]
    (hmem : L.essImage (limit (F ⋙ L))) : IsIso (limit.post F L) := by
  have : IsIso (adj.counit.app (limit (F ⋙ L))) :=
    (adj.isIso_counit_app_iff_mem_essImage).mpr hmem
  let e : limit F ≅ limit ((F ⋙ L) ⋙ R) :=
    HasLimit.isoOfNatIso (F.rightUnitor.symm ≪≫ Functor.isoWhiskerLeft F (asIso adj.unit))
  have hφ : adj.homEquiv _ _ (limit.post F L) =
      e.hom ≫ (preservesLimitIso R (F ⋙ L)).inv := by
    rw [Iso.eq_comp_inv]
    ext j
    rw [Category.assoc, preservesLimitIso_hom_π, ← adj.homEquiv_naturality_right, limit.post_π,
      Adjunction.homEquiv_unit, HasLimit.isoOfNatIso_hom_π]
    simp
  have : IsIso (adj.homEquiv _ _ (limit.post F L)) := by rw [hφ]; infer_instance
  rw [← (adj.homEquiv _ _).symm_apply_apply (limit.post F L), Adjunction.homEquiv_counit]
  infer_instance

end CategoryTheory

end
