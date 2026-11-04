module

public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.EpsilonDerivedBaseChange
public import StacksFrontier.AlgebraicGeometry.ProEtale.Cohomology.SuccUniverseCoefficients
public import StacksFrontier.RingTheory.Dualizing.DerivedHomBaseChange.Conservative
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.CompositeCohomologyBaseChange
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSquareCommShift
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowNaturalTransformations
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.LeftTExactness

/-!
# The pro-étale base change map at a torsion sheaf of `Λ`-modules coming from the étale site

Let
```
X' --g'--> X
|f'        |f
v          v
Y' --g---> Y
```
be a cartesian square of schemes with `f` proper, and let `ℋ` be a pro-étale sheaf of
`Λ`-modules on `X` which comes from `X_étale` and is killed by a positive integer. Then the base
change map `g⁻¹ Rf_* ℋ ⟶ Rf'_* (g')⁻¹ ℋ` is an isomorphism. Passing to underlying abelian sheaves
is conservative on derived categories and identifies the base change maps
(`AlgebraicGeometry.ProEtale.isIso_proetaleModuleDerivedBaseChange_app_iff_forget`), and the
underlying abelian sheaf of `ℋ` is `ε⁻¹` of a torsion abelian sheaf on `X_étale`, where
`AlgebraicGeometry.ProEtale.isIso_proetaleAbelianDerivedBaseChange_app_singleFunctor_epsilon`
applies.

## Main results

* `AlgebraicGeometry.ProEtale.isIso_proetaleModuleDerivedBaseChange_app_singleFunctor`.

Standard model: uses `Stacks.EtaleCohomology.etaleAbelianDerivedBaseChange`, which exists only
there.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.EtaleCohomology

universe u

namespace AlgebraicGeometry.ProEtale

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] hasSheafify_proEt_moduleCat_succ
  isGrothendieckAbelian_proetaleModuleSheaf_succ enoughInjectives_proetaleModuleSheaf_succ
  hasSheafify_proetale_addCommGrpCat_succ isGrothendieckAbelian_proetale_ab_succ
  preservesSheafification_forget₂_proetale_succ

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- An additive functor preserves annihilation of the identity by a natural number. -/
private theorem nsmul_id_obj_eq_zero {C D : Type*} [Category C] [Category D] [Preadditive C]
    [Preadditive D] (F : C ⥤ D) [F.Additive] {A : C} {m : ℕ} (h : m • 𝟙 A = 0) :
    m • 𝟙 (F.obj A) = 0 := by
  rw [← F.map_id, ← Functor.map_nsmul, h, Functor.map_zero]

/-- A pro-étale sheaf of `Λ`-modules coming from `X_étale` and killed by a positive integer has
underlying abelian sheaf `ε⁻¹` of a torsion abelian sheaf on `X_étale`. -/
theorem exists_epsilonInverseImage_iso_proetaleForget {X : Scheme.{u}}
    (H : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))
    (hH : (Scheme.etaleInverseImage.{u, 0, u + 1} X Λ).essImage H) (m : ℕ) (hm : 0 < m)
    (hmH : m • 𝟙 H = 0) :
    ∃ G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1},
      Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology G ∧
        Nonempty ((epsilonInverseImage.{u, 0} X).obj G ≅ (proetaleForget Λ X).obj H) := by
  obtain ⟨G, ⟨e⟩⟩ := (Scheme.etaleInverseImage_essImage_iff_forget₂.{0, u + 1} X Λ H).1 hH
  refine ⟨G, torsionSheafProperty_of_nsmul_id_eq_zero G m hm ?_, ⟨e⟩⟩
  have h₁ := nsmul_id_obj_eq_zero (proetaleForget Λ X) hmH
  have h₂ : (epsilonInverseImage.{u, 0} X).map (m • 𝟙 G) = 0 := by
    rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]
    have : m • 𝟙 ((epsilonInverseImage.{u, 0} X).obj G) =
        e.hom ≫ (m • 𝟙 ((proetaleForget Λ X).obj H)) ≫ e.inv := by
      simp
    rw [this, h₁]
    simp
  exact (epsilonAdjunction.{u, 0} X).fullyFaithfulLOfIsIsoUnit.map_injective
    (h₂.trans (Functor.map_zero _ _ _).symm)

/-- **The pro-étale base change map at a torsion sheaf of `Λ`-modules coming from the étale
site.** For a cartesian square with `f` proper and a pro-étale sheaf of `Λ`-modules `ℋ` on `X`
in the essential image of `ε⁻¹` and killed by a positive integer, the base change map
`g⁻¹ Rf_* ℋ ⟶ Rf'_* (g')⁻¹ ℋ` is an isomorphism. -/
theorem isIso_proetaleModuleDerivedBaseChange_app_singleFunctor
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (sq : IsPullback g' f' f g) (H : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))
    (hH : (Scheme.etaleInverseImage.{u, 0, u + 1} X Λ).essImage H) (m : ℕ) (hm : 0 < m)
    (hmH : m • 𝟙 H = 0) :
    IsIso ((proetaleModuleDerivedBaseChange.{u, u + 1, 0} f g f' g' sq.w.symm).app
      ((DerivedCategory.singleFunctor _ 0).obj H)) := by
  obtain ⟨G, hG, ⟨e⟩⟩ := exists_epsilonInverseImage_iso_proetaleForget Λ H hH m hm hmH
  have hab : IsIso ((proetaleAbelianDerivedBaseChange f g f' g' sq.w.symm).app
      ((DerivedCategory.singleFunctor _ 0).obj ((proetaleForget Λ X).obj H))) :=
    (NatTrans.isIso_app_iff_of_iso _ ((DerivedCategory.singleFunctor _ 0).mapIso e)).1
      (isIso_proetaleAbelianDerivedBaseChange_app_singleFunctor_epsilon f g g' f' sq G hG)
  obtain ⟨I, i, hi, hinj, hge⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective
      ((CochainComplex.singleFunctor (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ)) 0).obj
        H) 0
  have : IsIso (DerivedCategory.Q.map i) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ i).2 hi
  let e₁ : (DerivedCategory.singleFunctor _ 0).obj H ≅
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I) :=
    (DerivedCategory.singleFunctorIsoCompQ _ 0).app H ≪≫ asIso (DerivedCategory.Q.map i) ≪≫
      (DerivedCategory.quotientCompQhIso _).symm.app I
  let e₂ : (DerivedCategory.singleFunctor _ 0).obj ((proetaleForget Λ X).obj H) ≅
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj
        (((proetaleForget Λ X).mapHomologicalComplex _).obj I)) :=
    ((proetaleForget Λ X).mapDerivedCategorySingleFunctor 0).symm.app H ≪≫
      (proetaleForget Λ X).mapDerivedCategory.mapIso e₁ ≪≫
      (proetaleForget Λ X).mapDerivedCategoryFactorsh.app ((HomotopyCategory.quotient _ _).obj I)
  have h₁ := (isIso_proetaleModuleDerivedBaseChange_app_iff_forget Λ f g f' g' sq.w.symm I 0).1
    ((NatTrans.isIso_app_iff_of_iso _ e₂).1 hab)
  have h₂ : IsIso ((proetaleModuleDerivedBaseChange.{u, u + 1, 0} f g f' g' sq.w.symm).app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj I))) :=
    isIso_of_reflects_iso _ (proetaleForget Λ Y').mapDerivedCategory
  exact (NatTrans.isIso_app_iff_of_iso _ e₁).2 h₂

/-- The base change map of pro-étale sheaves of `Λ`-modules commutes with the shift: it is the
derived transformation of the underived base change map
(`Stacks.Homology.DerivedSquare.derivedSquare_eq_derivedBaseChangeMap`). -/
instance natTransCommShift_proetaleModuleDerivedBaseChange {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y)
    (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X) (w : f' ≫ g = g' ≫ f) :
    NatTrans.CommShift (proetaleModuleDerivedBaseChange.{u, u + 1, 0} (Λ := Λ) f g f' g' w) ℤ := by
  have := Stacks.Homology.DerivedSquare.natTransCommShift_derivedSquare
    (proetaleModuleBaseChange.{u, u + 1, 0} (Λ := Λ) f g f' g' w)
  rwa [Stacks.Homology.DerivedSquare.derivedSquare_eq_derivedBaseChangeMap] at this

/-- **The pro-étale base change map at a bounded below complex with torsion cohomology sheaves
coming from the étale site.** For a cartesian square with `f` proper and an object `E` of
`D(X_proétale, Λ)` which is bounded below, killed by a positive integer, and whose cohomology
sheaves come from `X_étale`, the base change map `g⁻¹ Rf_* E ⟶ Rf'_* (g')⁻¹ E` is an
isomorphism. -/
theorem isIso_proetaleModuleDerivedBaseChange_app_of_isGE
    {X Y X' Y' : Scheme.{u}} (f : X ⟶ Y) [IsProper f] (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
    (sq : IsPullback g' f' f g)
    (E : DerivedCategory (Sheaf (Scheme.ProEt.topology X) (ModuleCat.{u + 1} Λ))) (a : ℤ)
    (hE : E.IsGE a)
    (hH : ∀ q : ℤ, (Scheme.etaleInverseImage.{u, 0, u + 1} X Λ).essImage
      ((DerivedCategory.homologyFunctor _ q).obj E)) (m : ℕ) (hm : 0 < m) (hmE : m • 𝟙 E = 0) :
    IsIso ((proetaleModuleDerivedBaseChange.{u, u + 1, 0} f g f' g' sq.w.symm).app E) := by
  refine NatTrans.isIso_app_of_isGE
    (proetaleModuleDerivedBaseChange.{u, u + 1, 0} f g f' g' sq.w.symm)
    (fun L k hL ↦ ?_) (fun L k hL ↦ ?_) E a hE (fun q ↦ ?_)
  · have := hL
    exact Functor.isGE_obj_mapDerivedCategory _ _ k
      (Stacks.DerivedFunctor.isGE_totalRightDerived_obj
        (proetaleModuleDirectImage.{u, u + 1, 0} (Λ := Λ) f) L k)
  · have := Functor.isGE_obj_mapDerivedCategory (proetaleModuleInverseImage.{u, u + 1, 0} g' Λ)
      L k hL
    exact Stacks.DerivedFunctor.isGE_totalRightDerived_obj
      (proetaleModuleDirectImage.{u, u + 1, 0} (Λ := Λ) f') _ k
  · refine isIso_proetaleModuleDerivedBaseChange_app_singleFunctor Λ f g g' f' sq _ (hH q) m hm ?_
    exact nsmul_id_obj_eq_zero (DerivedCategory.homologyFunctor _ q) hmE

end AlgebraicGeometry.ProEtale

end
