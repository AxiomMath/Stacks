module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryInduced
public import
    StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.OpenImmersionRestrictionNaturality

/-!
# Composing left derived functors of exact functors

Let `F : A₀ ⥤ A₁`, `G : A₁ ⥤ A₂` and `H : A₀ ⥤ A₂` be exact functors of abelian categories with
`e : F ⋙ G ≅ H`, and let `LF`, `LG`, `LH` be total left derived functors of the three. Each is
the degreewise functor (`Stacks.Homology.leftDerivedIsoMapDerivedCategory`). A comparison
`c : LF ⋙ LG ⟶ LH` with the canonical factorization through the two counits and `e` is then,
under these identifications, the comparison `CategoryTheory.Functor.mapDerivedCategoryCompIso`
of degreewise functors. It is therefore induced, along the localizations of cochain complexes, by
the degreewise action of `e`.

## Main results

* `Stacks.Homology.comp_leftDerivedIsoMapDerivedCategory_hom`: the comparison corresponds to
  `CategoryTheory.Functor.mapDerivedCategoryCompIso e`.
* `Stacks.Homology.isInducedBy_of_leftDerived_comp`: the comparison is induced by the degreewise
  action of `e`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Homology

universe w₀ w₁ w₂ v₀ v₁ v₂ u₀ u₁ u₂

variable {A₀ : Type u₀} [Category.{v₀} A₀] [Abelian A₀] [HasDerivedCategory.{w₀} A₀]
  {A₁ : Type u₁} [Category.{v₁} A₁] [Abelian A₁] [HasDerivedCategory.{w₁} A₁]
  {A₂ : Type u₂} [Category.{v₂} A₂] [Abelian A₂] [HasDerivedCategory.{w₂} A₂]

/-- The factorization of a total left derived functor of an exact functor through the
localization of cochain complexes: it is the degreewise functor. -/
def leftDerivedFactors (F : A₀ ⥤ A₁) [F.Additive] [PreservesFiniteLimits F]
    [PreservesFiniteColimits F] (LF : DerivedCategory A₀ ⥤ DerivedCategory A₁)
    (α : DerivedCategory.Qh ⋙ LF ⟶
      F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [LF.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso A₀ (ComplexShape.up ℤ))] :
    DerivedCategory.Q ⋙ LF ≅ F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  Functor.isoWhiskerLeft DerivedCategory.Q (leftDerivedIsoMapDerivedCategory F LF α) ≪≫
    F.mapDerivedCategoryFactors

variable (F : A₀ ⥤ A₁) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  (G : A₁ ⥤ A₂) [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
  (H : A₀ ⥤ A₂) [H.Additive] [PreservesFiniteLimits H] [PreservesFiniteColimits H]
  (e : F ⋙ G ≅ H)
  (LF : DerivedCategory A₀ ⥤ DerivedCategory A₁)
  (αF : DerivedCategory.Qh ⋙ LF ⟶ F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
  [LF.IsLeftDerivedFunctor αF (HomotopyCategory.quasiIso A₀ (ComplexShape.up ℤ))]
  (LG : DerivedCategory A₁ ⥤ DerivedCategory A₂)
  (αG : DerivedCategory.Qh ⋙ LG ⟶ G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
  [LG.IsLeftDerivedFunctor αG (HomotopyCategory.quasiIso A₁ (ComplexShape.up ℤ))]
  (LH : DerivedCategory A₀ ⥤ DerivedCategory A₂)
  (αH : DerivedCategory.Qh ⋙ LH ⟶ H.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
  [LH.IsLeftDerivedFunctor αH (HomotopyCategory.quasiIso A₀ (ComplexShape.up ℤ))]
  (c : LF ⋙ LG ⟶ LH)
  (hc : ∀ J : HomotopyCategory A₀ (ComplexShape.up ℤ),
    c.app (DerivedCategory.Qh.obj J) ≫ αH.app J =
      LG.map (αF.app J) ≫ αG.app ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj J) ≫
        DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom.app
            J))

include hc in
/-- **A comparison of left derived functors of exact functors is the degreewise comparison.** -/
theorem comp_leftDerivedIsoMapDerivedCategory_hom :
    c ≫ (leftDerivedIsoMapDerivedCategory H LH αH).hom =
      NatTrans.hcomp (leftDerivedIsoMapDerivedCategory F LF αF).hom
          (leftDerivedIsoMapDerivedCategory G LG αG).hom ≫
        (Functor.mapDerivedCategoryCompIso e).hom := by
  suffices key : c = NatTrans.hcomp (leftDerivedIsoMapDerivedCategory F LF αF).hom
          (leftDerivedIsoMapDerivedCategory G LG αG).hom ≫
        (Functor.mapDerivedCategoryCompIso e).hom ≫ (leftDerivedIsoMapDerivedCategory H LH αH).inv
            by
    rw [key]
    simp
  refine Functor.leftDerived_ext LH αH (HomotopyCategory.quasiIso A₀ (ComplexShape.up ℤ)) _ _ _ ?_
  ext J
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Category.assoc]
  rw [hc J, ← leftDerivedIsoMapDerivedCategory_hom_app H LH αH J, Iso.inv_hom_id_app_assoc,
    Functor.mapDerivedCategoryCompIso_hom_app_Qh, NatTrans.hcomp_app']
  simp only [Category.assoc, Iso.inv_hom_id_app]
  rw [← leftDerivedIsoMapDerivedCategory_hom_app F LF αF J, Functor.map_comp, Category.assoc]
  refine congrArg (fun t => _ ≫ t) ?_
  have nat := (leftDerivedIsoMapDerivedCategory G LG αG).hom.naturality
    (F.mapDerivedCategoryFactorsh.hom.app J)
  dsimp at nat
  dsimp only [Functor.comp_obj]
  rw [Category.comp_id, ← reassoc_of% nat]
  exact congrArg (fun t => LG.map (F.mapDerivedCategoryFactorsh.hom.app J) ≫ t)
    ((reassoc_of% (leftDerivedIsoMapDerivedCategory_hom_app G LG αG
      ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj J))) _).symm

include hc in
/-- **A comparison of left derived functors of exact functors is induced degreewise** by the
comparison `e` acting on cochain complexes. -/
theorem isInducedBy_of_leftDerived_comp :
    NatTrans.IsInducedBy
      (Functor.compFactorization (leftDerivedFactors F LF αF) (leftDerivedFactors G LG αG))
      (leftDerivedFactors H LH αH) c
      (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom := fun K => by
  have h₁ := NatTrans.congr_app (comp_leftDerivedIsoMapDerivedCategory_hom F G H e LF αF LG αG LH αH
    c hc) (DerivedCategory.Q.obj K)
  have h₂ := Functor.mapDerivedCategoryCompIso_isInducedBy e K
  simp only [NatTrans.comp_app] at h₁
  simp only [leftDerivedFactors, Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.compFactorization_hom_app, Functor.map_comp,
    Category.assoc] at h₂ ⊢
  rw [reassoc_of% h₁, h₂, NatTrans.hcomp_app']
  simp only [Category.assoc]
  refine congrArg (fun t => _ ≫ t) ?_
  have nat := (leftDerivedIsoMapDerivedCategory G LG αG).hom.naturality
    (F.mapDerivedCategoryFactors.hom.app K)
  dsimp at nat
  rw [reassoc_of% nat]

end Stacks.Homology
