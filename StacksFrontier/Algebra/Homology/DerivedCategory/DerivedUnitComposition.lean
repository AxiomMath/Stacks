module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSquare
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Localization.RestrictionOfModules

/-!
# Complexes computing a total right derived functor, and composition

For an additive functor `F` out of a Grothendieck abelian category, say that a complex `M`
*computes* `RF` when the derived-functor unit `F(M) ⟶ RF(M)` is an isomorphism (Leray's
acyclicity, for unbounded complexes). This file records three facts about that condition.

* It can be read on one K-injective resolution: for a quasi-isomorphism `q : M ⟶ N` with `N`
  K-injective, `M` computes `RF` exactly when `F(q)` is a quasi-isomorphism.
* An exact functor is computed by every complex.
* **Composition.** If `F₁` carries K-injective complexes to complexes computing `RF₂`, and `M`
  computes `RF₁` and `F₁(M)` computes `RF₂`, then `M` computes `R(F₁ ⋙ F₂)` — for any functor
  isomorphic to `F₁ ⋙ F₂`. This is the content of `R(F₂ ∘ F₁) = RF₂ ∘ RF₁` (Stacks 015M) used
  at a single complex, with no comparison isomorphism of derived functors to be built.

## Main results

* `Stacks.Homology.DerivedSquare.isIso_totalRightDerivedUnit_app_iff_of_quasiIso`
* `Stacks.Homology.DerivedSquare.isIso_totalRightDerivedUnit_app_of_exact`
* `Stacks.Homology.DerivedSquare.isIso_totalRightDerivedUnit_app_of_comp` and its converse
  `Stacks.Homology.DerivedSquare.isIso_totalRightDerivedUnit_app_comp_iff`
* `Stacks.Homology.DerivedSquare.isIso_map_totalRightDerivedUnit_app_iff`: **transport along
  an exact functor preserving K-injectives.** If `F ⋙ E' ≅ Φ ⋙ G` with `E'` exact and `Φ` exact
  and preserving K-injective complexes, then `E'` of the unit of `RF` at `M` is invertible
  exactly when the unit of `RG` at `Φ(M)` is (Stacks 0DGA, part (3), in the form of units).

## References

* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.SiteCohomologyPresheaf (totalRightDerivedCompUnit
  isRightDerivedFunctor_totalRightDerived_comp totalRightDerivedCompUnit_app)

universe wA wB wC vA vB vC uA uB uC wG wG'

namespace Stacks.Homology.DerivedSquare

variable {A : Type uA} [Category.{vA} A] [Abelian A] [IsGrothendieckAbelian.{wG} A]
  [HasDerivedCategory.{wA} A]
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  {C : Type uC} [Category.{vC} C] [Abelian C] [HasDerivedCategory.{wC} C]

/-- **A complex computes `RF` exactly when `F` of one K-injective resolution of it is a
quasi-isomorphism.** -/
theorem isIso_totalRightDerivedUnit_app_iff_of_quasiIso (F : A ⥤ B) [F.Additive]
    [(F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    {M N : CochainComplex A ℤ} (q : M ⟶ N) (hq : QuasiIso q) [N.IsKInjective] :
    IsIso ((totalRightDerivedUnit F).app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj M))
      ↔ IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map q))) := by
  have hN : IsIso ((totalRightDerivedUnit F).app
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj N)) :=
    Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective _ _ _ N
  have hq' : IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map q)) :=
    Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) _
      ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2 hq)
  have hR : IsIso ((DerivedCategory.Qh ⋙ totalRightDerived F).map
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map q)) := by
    rw [Functor.comp_map]
    infer_instance
  rw [← isIso_comp_right_iff _ ((DerivedCategory.Qh ⋙ totalRightDerived F).map
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map q)),
    ← (totalRightDerivedUnit F).naturality
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map q),
    isIso_comp_right_iff]
  rfl

/-- **An exact functor is computed by every complex.** -/
theorem isIso_totalRightDerivedUnit_app_of_exact (F : A ⥤ B) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [(F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (M : CochainComplex A ℤ) :
    IsIso ((totalRightDerivedUnit F).app
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj M)) := by
  obtain ⟨N, q, hN, hq⟩ := Stacks.Cohomology.Localization.enoughKInjectives M
  rw [isIso_totalRightDerivedUnit_app_iff_of_quasiIso F q hq]
  exact Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso B (ComplexShape.up ℤ)) _
    ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2
      ((HomologicalComplex.mem_quasiIso_iff _).2 inferInstance))

/-- Under `e : F₁ ⋙ F₂ ≅ F`, `F(q)` and `F₂(F₁(q))` become invertible in the derived category
simultaneously. -/
private theorem isIso_map_comp_iff {X Y : Type*} [Category X] [Abelian X] [Category Y] [Abelian Y]
    {F₁ : X ⥤ Y} [F₁.Additive] {F₂ : Y ⥤ C} [F₂.Additive] {F : X ⥤ C} [F.Additive]
    (e : F₁ ⋙ F₂ ≅ F) {M N : CochainComplex X ℤ} (q : M ⟶ N) :
    IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map q))) ↔
    IsIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).map
      ((F₂.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((F₁.mapHomologicalComplex (ComplexShape.up ℤ)).map q)))) := by
  have he := (NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).hom.naturality q
  have hFq : (F.mapHomologicalComplex (ComplexShape.up ℤ)).map q =
      (NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).inv.app M ≫
        (F₂.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((F₁.mapHomologicalComplex (ComplexShape.up ℤ)).map q) ≫
        (NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).hom.app N := by
    have he' : (F₂.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((F₁.mapHomologicalComplex (ComplexShape.up ℤ)).map q) ≫
        (NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).hom.app N =
        (NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).hom.app M ≫
          (F.mapHomologicalComplex (ComplexShape.up ℤ)).map q := he
    rw [he', Iso.inv_hom_id_app_assoc]
  rw [hFq, Functor.map_comp, Functor.map_comp, Functor.map_comp, Functor.map_comp,
    isIso_comp_left_iff, isIso_comp_right_iff]

/-- **Composition.** Let `F₁ : A ⥤ B` carry K-injective complexes to complexes computing `RF₂`,
and let `F` be isomorphic to `F₁ ⋙ F₂`. If `M` computes `RF₁` and `F₁(M)` computes `RF₂`, then
`M` computes `RF`. -/
theorem isIso_totalRightDerivedUnit_app_of_comp [IsGrothendieckAbelian.{wG'} B]
    (F₁ : A ⥤ B) [F₁.Additive] (F₂ : B ⥤ C) [F₂.Additive] (F : A ⥤ C) [F.Additive]
    (e : F₁ ⋙ F₂ ≅ F)
    [(F₁.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    [(F₂.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso B (ComplexShape.up ℤ))]
    [(F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (h₁ : ∀ (I : CochainComplex A ℤ) [I.IsKInjective], IsIso ((totalRightDerivedUnit F₂).app
      ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
        ((F₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj I))))
    (M : CochainComplex A ℤ)
    (hM₁ : IsIso ((totalRightDerivedUnit F₁).app
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj M)))
    (hM₂ : IsIso ((totalRightDerivedUnit F₂).app
      ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
        ((F₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj M)))) :
    IsIso ((totalRightDerivedUnit F).app
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj M)) := by
  obtain ⟨N, q, hN, hq⟩ := Stacks.Cohomology.Localization.enoughKInjectives M
  rw [isIso_totalRightDerivedUnit_app_iff_of_quasiIso F₁ q hq] at hM₁
  rw [isIso_totalRightDerivedUnit_app_iff_of_quasiIso F q hq]
  have hN₂ := h₁ N
  have hR : IsIso ((DerivedCategory.Qh ⋙ totalRightDerived F₂).map
      ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
        ((F₁.mapHomologicalComplex (ComplexShape.up ℤ)).map q))) := by
    rw [Functor.comp_map]
    infer_instance
  have h₂ : IsIso ((F₂.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).map
      ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).map
        ((F₁.mapHomologicalComplex (ComplexShape.up ℤ)).map q))) := by
    rw [← isIso_comp_right_iff _ ((totalRightDerivedUnit F₂).app
      ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
        ((F₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj N))),
      (totalRightDerivedUnit F₂).naturality]
    infer_instance
  exact (isIso_map_comp_iff e q).2 h₂

/-- **Composition, read the other way.** Let `F₁ : A ⥤ B` preserve K-injective complexes, let
`F` be isomorphic to `F₁ ⋙ F₂`, and let `M` compute `RF₁`. Then `M` computes `RF` exactly when
`F₁(M)` computes `RF₂`: both say that `F` resp. `F₂` of one K-injective resolution of `M`, resp.
of its image under `F₁` (a K-injective resolution of `F₁(M)`), is a quasi-isomorphism. -/
theorem isIso_totalRightDerivedUnit_app_comp_iff [IsGrothendieckAbelian.{wG'} B]
    (F₁ : A ⥤ B) [F₁.Additive] (F₂ : B ⥤ C) [F₂.Additive] (F : A ⥤ C) [F.Additive]
    (e : F₁ ⋙ F₂ ≅ F)
    [(F₁.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    [(F₂.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso B (ComplexShape.up ℤ))]
    [(F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (h₁ : ∀ (I : CochainComplex A ℤ) [I.IsKInjective],
      CochainComplex.IsKInjective ((F₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj I))
    (M : CochainComplex A ℤ)
    (hM₁ : IsIso ((totalRightDerivedUnit F₁).app
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj M))) :
    IsIso ((totalRightDerivedUnit F).app
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj M)) ↔
      IsIso ((totalRightDerivedUnit F₂).app
        ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj
          ((F₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj M))) := by
  obtain ⟨N, q, hN, hq⟩ := Stacks.Cohomology.Localization.enoughKInjectives M
  rw [isIso_totalRightDerivedUnit_app_iff_of_quasiIso F₁ q hq] at hM₁
  have hq₁ : QuasiIso ((F₁.mapHomologicalComplex (ComplexShape.up ℤ)).map q) := by
    rw [← DerivedCategory.isIso_Q_map_iff_quasiIso]
    exact (NatIso.isIso_map_iff (DerivedCategory.quotientCompQhIso B) _).mp hM₁
  have := h₁ N
  rw [isIso_totalRightDerivedUnit_app_iff_of_quasiIso F q hq,
    isIso_totalRightDerivedUnit_app_iff_of_quasiIso F₂ _ hq₁]
  exact isIso_map_comp_iff e q

section Transport

variable {A' : Type*} [Category* A'] [Abelian A'] [IsGrothendieckAbelian.{wG'} A']
  [HasDerivedCategory A']
  {B' : Type*} [Category* B'] [Abelian B'] [HasDerivedCategory B']
  (F : A ⥤ B) [F.Additive] (G : A' ⥤ B') [G.Additive]
  [(F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasRightDerivedFunctor
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
  [(G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh).HasRightDerivedFunctor
    (HomotopyCategory.quasiIso A' (ComplexShape.up ℤ))]
  (E' : B ⥤ B') [E'.Additive] [PreservesFiniteLimits E'] [PreservesFiniteColimits E']
  (Φ : A ⥤ A') [Φ.Additive] [PreservesFiniteLimits Φ] [PreservesFiniteColimits Φ]

/-- The derived-functor unit exhibiting `Φ ⋙ RG` as a right derived functor of degreewise
`Φ ⋙ G`. -/
def exactThenDerivedUnit :
    Φ.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ⟶
      DerivedCategory.Qh ⋙ (Φ.mapDerivedCategory ⋙ totalRightDerived G) :=
  Functor.whiskerLeft (Φ.mapHomotopyCategory (ComplexShape.up ℤ)) (totalRightDerivedUnit G) ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight Φ.mapDerivedCategoryFactorsh.inv (totalRightDerived G) ≫
    (Functor.associator _ _ _).hom

omit [IsGrothendieckAbelian.{wG} A] [IsGrothendieckAbelian.{wG'} A'] in
/-- The component of `exactThenDerivedUnit G Φ` at `M` is the component of the unit of `RG` at
the image of `M` under `Φ`, followed by `RG` applied to the comparison of `Φ` on homotopy and
derived categories. -/
theorem exactThenDerivedUnit_app (M : HomotopyCategory A (ComplexShape.up ℤ)) :
    (exactThenDerivedUnit G Φ).app M =
      (totalRightDerivedUnit G).app ((Φ.mapHomotopyCategory (ComplexShape.up ℤ)).obj M) ≫
        (totalRightDerived G).map (Φ.mapDerivedCategoryFactorsh.inv.app M) := by
  simp [exactThenDerivedUnit]

/-- If `Φ` preserves K-injective complexes, `Φ ⋙ RG` is a right derived functor of degreewise
`Φ ⋙ G`. -/
theorem exactThenDerived_isRightDerivedFunctor
    (hΦ : ∀ (I : CochainComplex A ℤ) [I.IsKInjective],
      CochainComplex.IsKInjective ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :
    (Φ.mapDerivedCategory ⋙ totalRightDerived G).IsRightDerivedFunctor
      (exactThenDerivedUnit G Φ) (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) := by
  refine Stacks.Cohomology.Localization.rightDerived_of_kInjectives _ _ _ fun I _ => ?_
  rw [exactThenDerivedUnit_app]
  have := hΦ I
  have := Stacks.Cohomology.Localization.derivedUnit_isIsoOnKInjective
    (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) (totalRightDerived G)
    (totalRightDerivedUnit G) ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ this inferInstance

/-- The comparison, on homotopy categories, of degreewise `F` followed by `E'` with degreewise
`Φ` followed by degreewise `G`, attached to `τ : F ⋙ E' ≅ Φ ⋙ G`. -/
def exactSquareHomotopyIso (τ : F ⋙ E' ≅ Φ ⋙ G) :
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ⋙ E'.mapDerivedCategory ≅
      Φ.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        (G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) :=
  Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (F.mapHomotopyCategory (ComplexShape.up ℤ))
      E'.mapDerivedCategoryFactorsh ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight
      (Functor.mapHomotopyCategoryCompIso τ (ComplexShape.up ℤ) ≪≫
        (Functor.mapHomotopyCategoryCompIso (Iso.refl (Φ ⋙ G)) (ComplexShape.up ℤ)).symm)
      DerivedCategory.Qh ≪≫
    Functor.associator _ _ _

/-- **Transport of the derived-functor unit along an exact functor preserving K-injectives.**
For `τ : F ⋙ E' ≅ Φ ⋙ G` with `E'` exact and `Φ` exact and preserving K-injective complexes,
`E'` of the unit of `RF` at a complex `M` is invertible exactly when the unit of `RG` at `Φ(M)`
is. The composites `RF ⋙ E'` and `Φ ⋙ RG` are right derived functors of isomorphic functors,
and the isomorphism of derived functors they induce is compatible with the units. -/
theorem isIso_map_totalRightDerivedUnit_app_iff
    (hΦ : ∀ (I : CochainComplex A ℤ) [I.IsKInjective],
      CochainComplex.IsKInjective ((Φ.mapHomologicalComplex (ComplexShape.up ℤ)).obj I))
    (τ : F ⋙ E' ≅ Φ ⋙ G) (M : HomotopyCategory A (ComplexShape.up ℤ)) :
    IsIso (E'.mapDerivedCategory.map ((totalRightDerivedUnit F).app M)) ↔
      IsIso ((totalRightDerivedUnit G).app
        ((Φ.mapHomotopyCategory (ComplexShape.up ℤ)).obj M)) := by
  have := isRightDerivedFunctor_totalRightDerived_comp
    (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) E'.mapDerivedCategory
  have := exactThenDerived_isRightDerivedFunctor G Φ hΦ
  let τ' := exactSquareHomotopyIso F G E' Φ τ
  have fac := NatTrans.congr_app (Functor.rightDerivedNatTrans_fac
    (totalRightDerived F ⋙ E'.mapDerivedCategory) (Φ.mapDerivedCategory ⋙ totalRightDerived G)
    (totalRightDerivedCompUnit
      (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) E'.mapDerivedCategory)
    (exactThenDerivedUnit G Φ) (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) τ'.hom) M
  let τD := Functor.rightDerivedNatTrans
    (totalRightDerived F ⋙ E'.mapDerivedCategory) (Φ.mapDerivedCategory ⋙ totalRightDerived G)
    (totalRightDerivedCompUnit
      (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) E'.mapDerivedCategory)
    (exactThenDerivedUnit G Φ) (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) τ'.hom
  have hτD : IsIso τD := (Functor.rightDerivedNatIso
    (totalRightDerived F ⋙ E'.mapDerivedCategory) (Φ.mapDerivedCategory ⋙ totalRightDerived G)
    (totalRightDerivedCompUnit
      (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) E'.mapDerivedCategory)
    (exactThenDerivedUnit G Φ) (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) τ').isIso_hom
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, totalRightDerivedCompUnit_app] at fac
  rw [← isIso_comp_right_iff _ (τD.app (DerivedCategory.Qh.obj M)), fac, isIso_comp_left_iff,
    exactThenDerivedUnit_app, isIso_comp_right_iff]

end Transport

end Stacks.Homology.DerivedSquare

end
