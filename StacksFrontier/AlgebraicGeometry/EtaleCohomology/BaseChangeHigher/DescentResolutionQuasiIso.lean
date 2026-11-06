module

public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianBaseChangeMap
public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionOfRightDerivedFunctors
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedBaseChangePlus

/-!
# The degreewise base change comparison through acyclic resolutions, from the derived one

Let `τ : F ⋙ G ⟶ G' ⋙ F'` be a comparison of composites of additive functors between abelian
categories, with `G`, `G'` exact, and `Stacks.Cohomology.BaseChange.derived` its descent
`RF ⋙ RG ⟶ RG' ⋙ RF'` to the bounded below derived categories. Let `K` be a bounded below complex
whose terms are right acyclic for `F`, and `q : G'(K) ⟶ K'` a quasi-isomorphism onto a bounded
below complex whose terms are right acyclic for `F'`. If the descent is invertible at `K`, then
the morphism of complexes `τ_K ≫ F'(q) : G(F(K)) ⟶ F'(K')` is a quasi-isomorphism
(`Stacks.Cohomology.BaseChange.isIso_Q_map_comp_of_isIso_derived`).

## Main results

* `Stacks.Cohomology.BaseChange.isIso_Q_map_comp_of_isIso_derived`: if the derived descent is
  invertible at `K`, then `τ_K ≫ F'(q)` is a quasi-isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.BaseChange

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [EnoughInjectives A] [EnoughInjectives B] [EnoughInjectives C]
  (F : A ⥤ B) (F' : C ⥤ D) (G : B ⥤ D) (G' : A ⥤ C)
  [F.Additive] [F'.Additive] [G.Additive] [G'.Additive]

/-- **The degreewise base change comparison through acyclic resolutions.** If the descent
`RF ⋙ RG ⟶ RG' ⋙ RF'` of `τ` is invertible at a bounded below complex `K` of `F`-acyclic objects,
the unit of `RG'` is invertible (e.g. `G'` exact) and `q : G'(K) ⟶ K'` is a quasi-isomorphism onto
a bounded below complex of `F'`-acyclic objects, then `τ_K ≫ F'(q)` is a quasi-isomorphism. -/
theorem isIso_Q_map_comp_of_isIso_derived (τ : F ⋙ G ⟶ G' ⋙ F')
    (e : G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ≅
      DerivedCategory.Plus.Qh ⋙ G.rightDerivedFunctorPlus)
    [IsIso G'.rightDerivedFunctorPlusUnith]
    (K : CochainComplex.Plus A) (hK : ∀ n : ℤ, F.rightAcyclic (K.obj.X n))
    (K' : CochainComplex.Plus C) (hK' : ∀ n : ℤ, F'.rightAcyclic (K'.obj.X n))
    (q : G'.mapCochainComplexPlus.obj K ⟶ K') (hq : QuasiIso q.hom)
    (hbc : IsIso ((derived F F' G G' τ e).app
      (DerivedCategory.Plus.Qh.obj ((HomotopyCategory.Plus.quotient A).obj K)))) :
    IsIso (DerivedCategory.Q.map ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app K.obj ≫
      (F'.mapHomologicalComplex (ComplexShape.up ℤ)).map q.hom)) := by
  let K₀ := (HomotopyCategory.Plus.quotient A).obj K
  let K₀' := (HomotopyCategory.Plus.quotient C).obj K'
  let X := (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (F ⋙ G))).hom.app K₀ ≫
    (mapPlus τ).app K₀ ≫ (Functor.mapHomotopyCategoryPlusCompIso (Iso.refl (G' ⋙ F'))).inv.app K₀
  have hfac := NatTrans.congr_app (derived_fac F F' G G' τ e) K₀
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Category.id_comp] at hfac
  have happ : (onHomotopy F F' G G' τ e).app K₀ =
      e.inv.app (F.mapHomotopyCategoryPlus.obj K₀) ≫ DerivedCategory.Plus.Qh.map X ≫
        F'.rightDerivedFunctorPlusUnith.app (G'.mapHomotopyCategoryPlus.obj K₀) ≫
        F'.rightDerivedFunctorPlus.map (G'.rightDerivedFunctorPlusUnith.app K₀) := by
    simp [onHomotopy, X]
  rw [happ] at hfac
  have hu : IsIso (F.rightDerivedFunctorPlusUnith.app K₀) :=
    Functor.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic F K₀ hK
  have hL : IsIso (G.rightDerivedFunctorPlus.map (F.rightDerivedFunctorPlusUnith.app K₀) ≫
      (derived F F' G G' τ e).app (DerivedCategory.Plus.Qh.obj K₀)) := inferInstance
  rw [hfac] at hL
  have hA : IsIso (DerivedCategory.Plus.Qh.map X ≫
      F'.rightDerivedFunctorPlusUnith.app (G'.mapHomotopyCategoryPlus.obj K₀)) := by
    have : IsIso (G'.rightDerivedFunctorPlusUnith.app K₀) :=
      NatIso.isIso_app_of_isIso G'.rightDerivedFunctorPlusUnith K₀
    have : IsIso (F'.rightDerivedFunctorPlus.map (G'.rightDerivedFunctorPlusUnith.app K₀)) :=
      Functor.map_isIso _ _
    have h1 : IsIso (DerivedCategory.Plus.Qh.map X ≫
        F'.rightDerivedFunctorPlusUnith.app (G'.mapHomotopyCategoryPlus.obj K₀) ≫
        F'.rightDerivedFunctorPlus.map (G'.rightDerivedFunctorPlusUnith.app K₀)) :=
      IsIso.of_isIso_comp_left (e.inv.app (F.mapHomotopyCategoryPlus.obj K₀)) _
    rw [← Category.assoc] at h1
    exact IsIso.of_isIso_comp_right _
      (F'.rightDerivedFunctorPlus.map (G'.rightDerivedFunctorPlusUnith.app K₀))
  let φ : G'.mapHomotopyCategoryPlus.obj K₀ ⟶ K₀' := (HomotopyCategory.Plus.quotient C).map q
  have hφ : IsIso (F'.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map φ)) := by
    have : IsIso (DerivedCategory.Plus.Qh.map φ) :=
      Localization.inverts DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso _) φ
        ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hq)
    infer_instance
  have hu' : IsIso (F'.rightDerivedFunctorPlusUnith.app K₀') :=
    Functor.isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic F' K₀' hK'
  have hnat := F'.rightDerivedFunctorPlusUnith.naturality φ
  simp only [Functor.comp_map] at hnat
  have hB : IsIso ((DerivedCategory.Plus.Qh.map X ≫
      DerivedCategory.Plus.Qh.map (F'.mapHomotopyCategoryPlus.map φ)) ≫
      F'.rightDerivedFunctorPlusUnith.app K₀') := by
    have e' : (DerivedCategory.Plus.Qh.map X ≫
        DerivedCategory.Plus.Qh.map (F'.mapHomotopyCategoryPlus.map φ)) ≫
        F'.rightDerivedFunctorPlusUnith.app K₀' =
      (DerivedCategory.Plus.Qh.map X ≫
        F'.rightDerivedFunctorPlusUnith.app (G'.mapHomotopyCategoryPlus.obj K₀)) ≫
        F'.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Qh.map φ) := by
      rw [Category.assoc, Category.assoc]
      exact congrArg (DerivedCategory.Plus.Qh.map X ≫ ·) hnat
    rw [e']
    exact IsIso.comp_isIso' hA hφ
  have hC : IsIso (DerivedCategory.Plus.Qh.map (X ≫ F'.mapHomotopyCategoryPlus.map φ)) := by
    rw [Functor.map_comp]
    exact IsIso.of_isIso_comp_right _ (F'.rightDerivedFunctorPlusUnith.app K₀')
  have hD : IsIso ((DerivedCategory.Plus.ι).map
      (DerivedCategory.Plus.Qh.map (X ≫ F'.mapHomotopyCategoryPlus.map φ))) := inferInstance
  have hE : IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.Plus.ι D).map (X ≫ F'.mapHomotopyCategoryPlus.map φ))) :=
    (NatIso.isIso_map_iff (DerivedCategory.Plus.QhCompιIsoιCompQh D) _).1 hD
  exact Stacks.Cohomology.DerivedBaseChangePlus.isIso_Q_map_of_isIso_Qh_map_eq _ _
    (@Stacks.Cohomology.DerivedBaseChangePlus.quotient_map_natTrans_comp_eq _ _ _ _ _ _ _ _ _ _ _ _
      F G G' F' inferInstance inferInstance inferInstance inferInstance inferInstance inferInstance
      τ K.obj K'.obj q.hom) hE

end Stacks.Cohomology.BaseChange

end
