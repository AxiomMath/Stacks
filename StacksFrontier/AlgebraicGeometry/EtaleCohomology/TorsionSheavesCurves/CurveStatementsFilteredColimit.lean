module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DirectSumsOfEtaleCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.RestrictionLongExactSequence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.CurveStatementsFiniteDirectImage

/-!
# Étale cohomology and restriction maps along filtered colimits

Let `X` be a quasi-compact quasi-separated scheme. Étale cohomology `H^q(X, -)`, in the form of
Mathlib's `CategoryTheory.Sheaf.H`, commutes with filtered colimits of abelian sheaves (Tag 03Q5),
and so does the restriction map `H^q(X, F) → H^q(Y, F|_Y)` along any morphism `Y ⟶ X` with `Y`
quasi-compact quasi-separated, inverse image being a left adjoint. Consequently vanishing,
bijectivity and surjectivity of these maps pass from the terms of a filtered colimit to the
colimit. These are the limit arguments of the proof of Theorem 03SC.

## Main results

* `Stacks.EtaleCohomology.preservesColimitsOfShape_functorH_smallEtale`: Tag 03Q5 for
  `CategoryTheory.Sheaf.functorH`.
* `Stacks.EtaleCohomology.etaleCohomologyRestrictionNatTrans`: restriction as a natural
  transformation.
* `Stacks.EtaleCohomology.subsingleton_sheafH_of_isColimit`,
  `Stacks.EtaleCohomology.bijective_etaleCohomologyRestrictionMap_of_isColimit` and
  `Stacks.EtaleCohomology.surjective_etaleCohomologyRestrictionMap_of_isColimit`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] Stacks.Cohomology.ColimitsOfCohomology.additive_sheafΓ
  hasExt_sheaf_smallEtale_succ

/-- Étale cohomology in degree `q` on `X`, as a functor on abelian sheaves at the coefficients
`AddCommGrpCat.{u + 1}`, with `Ext` taken in the universe `u + 1`. -/
abbrev smallEtaleFunctorH (X : Scheme.{u}) (q : ℕ) :
    Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1} ⥤ AddCommGrpCat.{u + 1} :=
  Sheaf.functorH X.smallEtaleTopology q

/-- **Tag 03Q5 for `Sheaf.H`.** On a quasi-compact quasi-separated scheme, étale cohomology in
each degree preserves filtered colimits of abelian sheaves. -/
theorem preservesColimitsOfShape_functorH_smallEtale (X : Scheme.{u}) [CompactSpace X]
    [QuasiSeparatedSpace X] (q : ℕ) (I : Type (u + 1)) [SmallCategory I] [IsFiltered I] :
    PreservesColimitsOfShape I
      (smallEtaleFunctorH X q) :=
  have := preservesColimitsOfShape_rightDerived_Γ_smallEtale.{0} X q I
  preservesColimitsOfShape_of_natIso
    (Cohomology.GlobalSections.rightDerivedΓIsoFunctorH.{u + 1} X.smallEtaleTopology q)

/-- Restriction on étale cohomology along `i : Y ⟶ X`, as a natural transformation from
`H^q(X, -)` to `H^q(Y, i^{-1}(-))`. -/
def etaleCohomologyRestrictionNatTrans {X Y : Scheme.{u}} (i : Y ⟶ X) (q : ℕ) :
    smallEtaleFunctorH X q ⟶
      etaleAbelianInverseImage.{u, 0} i ⋙
        smallEtaleFunctorH Y q where
  app F := AddCommGrpCat.ofHom (etaleCohomologyRestrictionMap.{u, 0, u + 1} i F q)
  naturality F G φ := by
    ext x
    exact etaleCohomologyRestrictionMap_comp_mk₀.{u, 0, u + 1} i φ q x

/-- Inverse image of étale abelian sheaves preserves colimits, being a left adjoint. -/
private theorem preservesColimitsOfShape_etaleAbelianInverseImage {X Y : Scheme.{u}} (i : Y ⟶ X)
    (I : Type (u + 1)) [SmallCategory I] :
    PreservesColimitsOfShape I (etaleAbelianInverseImage.{u, 0} i) :=
  (etaleAbelianInverseImageDirectImageAdj.{u, 0} i).leftAdjoint_preservesColimits
    |>.preservesColimitsOfShape

section Colimit

variable {X : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X] {I : Type (u + 1)}
  [SmallCategory I] [IsFiltered I] {D : I ⥤ Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}}
  {c : Cocone D} (hc : IsColimit c)

include hc

/-- **Vanishing passes to filtered colimits.** -/
theorem subsingleton_sheafH_of_isColimit (q : ℕ)
    (h : ∀ j, Subsingleton (Sheaf.H.{u + 1} (D.obj j) q)) :
    Subsingleton (Sheaf.H.{u + 1} c.pt q) := by
  have := preservesColimitsOfShape_functorH_smallEtale X q I
  change Subsingleton ((smallEtaleFunctorH X q).obj c.pt)
  refine AddCommGrpCat.isZero_iff_subsingleton.1 ((IsZero.iff_id_eq_zero _).2 ?_)
  refine (isColimitOfPreserves (smallEtaleFunctorH X q) hc).hom_ext fun j ↦ ?_
  exact (AddCommGrpCat.isZero_iff_subsingleton.2 (h j)).eq_of_src _ _

/-- **Bijectivity of restriction passes to filtered colimits.** -/
theorem bijective_etaleCohomologyRestrictionMap_of_isColimit {Y : Scheme.{u}} [CompactSpace Y]
    [QuasiSeparatedSpace Y] (i : Y ⟶ X) (q : ℕ)
    (h : ∀ j, Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, u + 1} i (D.obj j) q)) :
    Function.Bijective (etaleCohomologyRestrictionMap.{u, 0, u + 1} i c.pt q) := by
  have := preservesColimitsOfShape_functorH_smallEtale X q I
  have := preservesColimitsOfShape_functorH_smallEtale Y q I
  have := preservesColimitsOfShape_etaleAbelianInverseImage i I
  have : IsIso (Functor.whiskerLeft D (etaleCohomologyRestrictionNatTrans i q)) := by
    rw [NatTrans.isIso_iff_isIso_app]
    exact fun j ↦ (ConcreteCategory.isIso_iff_bijective _).2 (h j)
  exact (ConcreteCategory.isIso_iff_bijective _).1
    (isIso_app_coconePt_of_preservesColimit D (etaleCohomologyRestrictionNatTrans i q) c hc)

omit [CompactSpace X] [QuasiSeparatedSpace X] in
/-- **Surjectivity of restriction passes to filtered colimits.** -/
theorem surjective_etaleCohomologyRestrictionMap_of_isColimit {Y : Scheme.{u}} [CompactSpace Y]
    [QuasiSeparatedSpace Y] (i : Y ⟶ X) (q : ℕ)
    (h : ∀ j, Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1} i (D.obj j) q)) :
    Function.Surjective (etaleCohomologyRestrictionMap.{u, 0, u + 1} i c.pt q) := by
  have := preservesColimitsOfShape_functorH_smallEtale Y q I
  have := preservesColimitsOfShape_etaleAbelianInverseImage i I
  let α := etaleCohomologyRestrictionNatTrans i q
  let G := etaleAbelianInverseImage.{u, 0} i ⋙ smallEtaleFunctorH Y q
  have hepi : ∀ j, Epi (α.app (D.obj j)) := fun j ↦ (AddCommGrpCat.epi_iff_surjective _).2 (h j)
  refine (AddCommGrpCat.epi_iff_surjective (α.app c.pt)).1 ⟨fun {Z} u v huv ↦ ?_⟩
  refine (isColimitOfPreserves G hc).hom_ext fun j ↦ ?_
  rw [← cancel_epi (α.app (D.obj j))]
  change α.app (D.obj j) ≫ G.map (c.ι.app j) ≫ u = α.app (D.obj j) ≫ G.map (c.ι.app j) ≫ v
  rw [← Category.assoc, ← α.naturality, Category.assoc,
    show α.app (((Functor.const I).obj c.pt).obj j) = α.app c.pt from rfl, huv,
    ← Category.assoc]
  exact congrArg (· ≫ v) (α.naturality (c.ι.app j))

end Colimit

end Stacks.EtaleCohomology
