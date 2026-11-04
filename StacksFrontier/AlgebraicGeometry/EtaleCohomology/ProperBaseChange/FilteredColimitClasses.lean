module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ClosedPointSupport.BoundedSiteFilteredColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FilteredColimitsOfEtaleCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteDescent.ResolutionSpectralSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.RestrictionLongExactSequence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.RightDerivedSectionsEssentiallySmall

/-!
# Cohomology classes on a filtered colimit come from a stage

Let `X` be a quasi-compact and quasi-separated scheme and `D : I ⥤ Sheaf X_étale Ab` a filtered
system of abelian sheaves. By Stacks Project Tag 03Q5,
`Stacks.EtaleCohomology.isIso_colimit_post_rightDerived_Γ_smallEtale`, étale cohomology — there
the right derived functors of global sections — commutes with the colimit. This file restates
that for `CategoryTheory.Sheaf.H`, the `Ext`-groups out of the constant sheaf `ℤ` in which the
restriction maps of `Stacks.EtaleCohomology.etaleCohomologyRestrictionMap` are written: every
class in `H^q(X, colim D)` is the image of a class in some `H^q(X, D_i)`.

## Main results

* `Stacks.EtaleCohomology.extFunctorObjConstZeroIsoΓ`: `Ext⁰(ℤ, -) ≅ Γ`.
* `Stacks.EtaleCohomology.isIso_colimit_post_extFunctorObj_smallEtale`: `Ext^q(ℤ, -)` commutes
  with filtered colimits on a quasi-compact quasi-separated scheme.
* `Stacks.EtaleCohomology.exists_sheafH_eq_comp_of_isColimit`: classes come from a stage.
* `Stacks.EtaleCohomology.surjective_etaleCohomologyRestrictionMap_of_isColimit_of_qcqs`:
  surjectivity of a restriction map onto a quasi-compact quasi-separated scheme passes to filtered
  colimits.

## Implementation notes

The identification of `Ext^q(ℤ, -)` with the right derived functors of `Γ` is
`ModuleSheafCohomology.nonempty_extFunctorObj_iso_rightDerived_of_extZeroIso`, both being
universal δ-functors agreeing in degree zero. The coefficients are `AddCommGrpCat.{u + 1}` and
the `Ext` universe is `u + 1`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] isGrothendieckAbelian_sheaf_smallEtale_objectUniverse

variable (X : Scheme.{u})

/-- `Ext` of abelian sheaves on the small étale site, in the universe `u + 1`. -/
instance hasExt_sheaf_smallEtale_objectUniverse :
    HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  hasExt_of_enoughInjectives.{u + 1} _

/-- **Degree-zero `Ext` out of `ℤ` is global sections.** -/
def extFunctorObjConstZeroIsoΓ :
    extFunctorObj.{u + 1} (constZ X) 0 ≅ Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  NatIso.ofComponents
    (fun F ↦ (Sheaf.H.equiv₀ F (terminalIsTerminal (C := X.Etale))).toAddCommGrpIso)
    (fun {F G} f ↦ by
      ext x
      exact (Sheaf.H.equiv₀_naturality (terminalIsTerminal (C := X.Etale)) f x).symm) ≪≫
    (Sheaf.ΓNatIsoSheafSections X.smallEtaleTopology AddCommGrpCat.{u + 1}
      (terminalIsTerminal (C := X.Etale))).symm

/-- **`Ext^q(ℤ, -)` is the `q`-th right derived functor of global sections.** -/
lemma nonempty_extFunctorObj_constZ_iso_rightDerived (q : ℕ) :
    Nonempty (extFunctorObj.{u + 1} (constZ X) q ≅
      (Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerived q) :=
  ModuleSheafCohomology.nonempty_extFunctorObj_iso_rightDerived_of_extZeroIso _ _
    (extFunctorObjConstZeroIsoΓ X) q

/-- **Stacks 03Q5 for `Ext` out of `ℤ`.** -/
theorem isIso_colimit_post_extFunctorObj_smallEtale [CompactSpace X] [QuasiSeparatedSpace X]
    (q : ℕ) {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    (D : I ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    IsIso (colimit.post D (extFunctorObj.{u + 1} (constZ X) q)) := by
  have h := isIso_colimit_post_rightDerived_Γ_smallEtale.{0, u} X q D
  have : PreservesColimit D ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerived q) :=
    preservesColimit_of_isIso_post _ D
  have : PreservesColimit D (extFunctorObj.{u + 1} (constZ X) q) :=
    preservesColimit_of_natIso D (nonempty_extFunctorObj_constZ_iso_rightDerived X q).some.symm
  infer_instance

/-- **Classes on a filtered colimit come from a stage.** On a quasi-compact quasi-separated
scheme, every class in `H^q(X, c.pt)`, for `c` a colimit cocone of a filtered system `D` of
abelian sheaves, is the image of a class in some `H^q(X, D_i)`. -/
theorem exists_sheafH_eq_comp_of_isColimit [CompactSpace X] [QuasiSeparatedSpace X]
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    {D : I ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} {c : Cocone D}
    (hc : IsColimit c) (q : ℕ) (y : Sheaf.H.{u + 1} c.pt q) :
    ∃ (i : I) (x : Sheaf.H.{u + 1} (D.obj i) q),
      x.comp (Ext.mk₀ (c.ι.app i)) (add_zero q) = y := by
  let E := extFunctorObj.{u + 1} (constZ X) q
  have := isIso_colimit_post_extFunctorObj_smallEtale X q D
  let e : colimit D ≅ c.pt := colimit.isoColimitCocone ⟨c, hc⟩
  have hb : Function.Bijective (colimit.post D E ≫ E.map e.hom) :=
    (ConcreteCategory.isIso_iff_bijective _).mp inferInstance
  obtain ⟨z, hz⟩ := hb.2 y
  obtain ⟨i, x, rfl⟩ := Concrete.colimit_exists_rep (D ⋙ E) z
  refine ⟨i, x, ?_⟩
  rw [← hz]
  have h1 : colimit.ι (D ⋙ E) i ≫ colimit.post D E ≫ E.map e.hom = E.map (c.ι.app i) := by
    rw [colimit.ι_post_assoc, ← E.map_comp, colimit.isoColimitCocone_ι_hom]
  exact (ConcreteCategory.congr_hom h1 x).symm

/-- **Surjectivity of restriction passes to filtered colimits.** For `i : Y ⟶ X` with `Y`
quasi-compact and quasi-separated, if restriction along `i` is surjective in degree `q` on every
member of a filtered system of abelian sheaves, it is surjective in degree `q` on its colimit.
Inverse image is a left adjoint, so it carries the colimit cocone to a colimit cocone, and the
restriction maps are natural in the sheaf. -/
theorem surjective_etaleCohomologyRestrictionMap_of_isColimit_of_qcqs {Y : Scheme.{u}} (i : Y ⟶ X)
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    {I : Type (u + 1)} [SmallCategory I] [IsFiltered I]
    {D : I ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} {c : Cocone D}
    (hc : IsColimit c) (q : ℕ)
    (h : ∀ j, Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1} i (D.obj j) q)) :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1} i c.pt q) := by
  intro y
  have hc' := isColimitOfPreserves (etaleAbelianInverseImage.{u, 0} i) hc
  obtain ⟨j, x', hx'⟩ := exists_sheafH_eq_comp_of_isColimit Y hc' q y
  obtain ⟨x, rfl⟩ := h j x'
  exact ⟨x.comp (Ext.mk₀ (c.ι.app j)) (add_zero q),
    (etaleCohomologyRestrictionMap_comp_mk₀.{u, 0, u + 1} i (c.ι.app j) q x).trans hx'⟩

end Stacks.EtaleCohomology

end
