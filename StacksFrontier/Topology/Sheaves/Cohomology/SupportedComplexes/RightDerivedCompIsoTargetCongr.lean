module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedCompIsoSpellings
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose

/-!
# Varying the target functor in `Stacks.Cohomology.ModuleComparison.rightDerivedCompIso`

For additive `F : 𝒞 ⥤ 𝒟`, additive and exact `G : 𝒟 ⥤ ℰ`, additive `H : 𝒞 ⥤ ℰ` and a comparison
`e : F ⋙ G ≅ H`, the isomorphism `F.rightDerived n ⋙ G ≅ H.rightDerived n` given by
`Stacks.Cohomology.ModuleComparison.rightDerivedCompIso F G H e n` is its value at
`CategoryTheory.Iso.refl (F ⋙ G)` followed by the right derived functor of `e`.

## Main results

* `Stacks.DerivedIndexing.rightDerivedCompIso_eq_refl_trans`: the comparison at a general `e` is
  the comparison at `CategoryTheory.Iso.refl` followed by the right derived functor of `e`.
  Componentwise form `Stacks.DerivedIndexing.rightDerivedCompIso_hom_app_eq_refl_trans`.
* `Stacks.DerivedIndexing.moduleComparison_rightDerivedCompIso_hom_app`: componentwise,
  `Stacks.Cohomology.ModuleComparison.rightDerivedCompIso F G H e n` is the inverse of Mathlib's
  `CategoryTheory.Functor.rightDerivedCompIso F G n` followed by the right derived functor of `e`.
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits

namespace Stacks.DerivedIndexing

universe v v' v'' u u' u''

variable {C : Type u} {D : Type u'} {E : Type u''}
  [Category.{v} C] [Category.{v'} D] [Category.{v''} E]
  [Abelian C] [Abelian D] [Abelian E] [EnoughInjectives C]
  (F : C ⥤ D) [F.Additive] (G : D ⥤ E) [G.Additive] [G.PreservesHomology]
  (H : C ⥤ E) [H.Additive] (e : F ⋙ G ≅ H)

/-- The component at `M` of `Stacks.Cohomology.ModuleComparison.rightDerivedCompIso F G H e n` is
its component at `CategoryTheory.Iso.refl (F ⋙ G)` followed by
`CategoryTheory.NatTrans.rightDerived e.hom n`. -/
theorem rightDerivedCompIso_hom_app_eq_refl_trans (n : ℕ) (M : C) :
    (Stacks.Cohomology.ModuleComparison.rightDerivedCompIso F G H e n).hom.app M =
      (Stacks.Cohomology.ModuleComparison.rightDerivedCompIso F G (F ⋙ G)
          (Iso.refl (F ⋙ G)) n).hom.app M ≫
        (NatTrans.rightDerived e.hom n).app M := by
  rw [Stacks.Cohomology.DerivedCompTransport.rightDerivedCompIso_hom_app F G H e n M,
    Stacks.Cohomology.DerivedCompTransport.rightDerivedCompIso_hom_app F G (F ⋙ G)
      (Iso.refl (F ⋙ G)) n M,
    mapComplexHomologyIso_hom_app F G H e n (injectiveResolution M).cocomplex,
    mapComplexHomologyIso_refl_hom_app F G n (injectiveResolution M).cocomplex,
    InjectiveResolution.rightDerived_app_eq e.hom (injectiveResolution M) n]
  exact splice _ _ _ _ _ _ (Iso.inv_hom_id _)

/-- For additive `F`, additive and exact `G`, additive `H` and `e : F ⋙ G ≅ H`, the comparison
`F.rightDerived n ⋙ G ≅ H.rightDerived n` at `e` is the comparison at
`CategoryTheory.Iso.refl (F ⋙ G)` followed by the degree-`n` right derived functor of `e`. -/
theorem rightDerivedCompIso_eq_refl_trans (n : ℕ) :
    Stacks.Cohomology.ModuleComparison.rightDerivedCompIso F G H e n =
      Stacks.Cohomology.ModuleComparison.rightDerivedCompIso F G (F ⋙ G)
          (Iso.refl (F ⋙ G)) n ≪≫
        Functor.rightDerivedIsoOfNatIso e n :=
  Iso.ext (NatTrans.ext (funext fun M =>
    rightDerivedCompIso_hom_app_eq_refl_trans F G H e n M))

/-- The two spellings of pulling an exact functor out of a right derived functor agree at a
general comparison, componentwise. -/
theorem moduleComparison_rightDerivedCompIso_hom_app (n : ℕ) (M : C) :
    (Stacks.Cohomology.ModuleComparison.rightDerivedCompIso F G H e n).hom.app M =
      (F.rightDerivedCompIso G n).inv.app M ≫ (NatTrans.rightDerived e.hom n).app M := by
  rw [rightDerivedCompIso_hom_app_eq_refl_trans F G H e n M,
    moduleComparison_rightDerivedCompIso_refl_app F G n M]

end Stacks.DerivedIndexing

end
