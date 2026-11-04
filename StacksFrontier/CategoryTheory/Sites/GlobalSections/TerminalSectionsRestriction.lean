module

public import StacksFrontier.CategoryTheory.Sites.GlobalSections.RestrictionOfGlobalSections

/-!
# Sections at two terminal objects, for an arbitrary coefficient category

`CategoryTheory.Sheaf.ΓNatIsoSheafSections` identifies global sections with the sections over a
terminal object of the site. For two terminal objects `T` and `T'`, the two identifications
differ by restriction along the unique arrow `T' ⟶ T`. For sheaves of types this is
`CategoryTheory.Sheaf.ΓNatIsoSheafSections_hom_app_map`; this file proves it for sheaves with
values in an arbitrary category, from the evaluation
`CategoryTheory.Sheaf.ΓNatIsoSheafSections_hom_app_general`.

## Main results

* `CategoryTheory.Sheaf.ΓNatIsoSheafSections_hom_app_map_general` — the statement above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v u' v'

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A : Type u'} [Category.{v'} A] [HasWeakSheafify J A] [HasTerminal C]

/-- **The identifications of global sections with the sections at two terminal objects differ by
restriction.** For terminal objects `T` and `T'` of the site and the unique arrow `f : T' ⟶ T`,
composing the identification at `T` with restriction along `f` gives the identification at
`T'`, for sheaves with values in any category. -/
theorem ΓNatIsoSheafSections_hom_app_map_general {T T' : C} (hT : IsTerminal T)
    (hT' : IsTerminal T') (f : T' ⟶ T) (F : Sheaf J A) :
    (ΓNatIsoSheafSections J A hT).hom.app F ≫ F.obj.map f.op =
      (ΓNatIsoSheafSections J A hT').hom.app F := by
  rw [ΓNatIsoSheafSections_hom_app_general, ΓNatIsoSheafSections_hom_app_general]
  exact F.ΓRes_map f.op

end CategoryTheory.Sheaf

end
