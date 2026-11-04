module

public import
  StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.ProjectionFormulaLocallySmall
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ModelComparison

/-!
# The comparison of the two derived tensor products respects the maps to `Tot(K ⊗ L)`

A ringed site `X` carries two canonical derived tensor products: that of
`Stacks.DerivedTensor.RingedSite` over its structure sheaf and that of `Stacks.SheafOfModules`
over the site. Both come with a canonical map `K ⊗ᴸ L ⟶ Tot(K ⊗ L)` to the ordinary total tensor
complex, for arbitrary complexes `K, L`. The comparison
`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorIsoSheafOfModules` intertwines them.

## Main results

* `derivedTensorProductFunctorIsoSheafOfModules_hom_app_app_toTensor`: the comparison intertwines
  the two maps `K ⊗ᴸ L ⟶ Tot(K ⊗ L)`.
* `Stacks.Duality.ProjectionFormulaLocallySmall.standardTensorIso_hom_app_app_toTensor`: the same
  on a scheme, at the standard model.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.DerivedTensor.RingedSite

variable (X : AlgebraicGeometry.RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory (Modules X.O)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj M).Additive]
  [∀ (K L : CochainComplex (Modules X.O) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-- If `a ≫ b = 𝟙` and `b ≫ c' = c`, then `(a ≫ c ≫ d⁻¹) ≫ d = c'`. -/
private lemma comp_comp_inv_comp_hom {D : Type*} [Category D] {A B C E : D} (a : A ⟶ B)
    (b : B ⟶ A) (c : B ⟶ C) (c' : A ⟶ C) (d : E ≅ C) (hab : a ≫ b = 𝟙 A) (h : b ≫ c' = c) :
    (a ≫ c ≫ d.inv) ≫ d.hom = c' := by
  rw [Category.assoc, Category.assoc, Iso.inv_hom_id, Category.comp_id, ← h, ← Category.assoc,
    hab, Category.id_comp]

/-- If `α₀ ≫ t₀ = s₀`, the squares `hB`, `hA`, `ht` and `hs` commute and `A ≫ B` is an
epimorphism, then `α ≫ t = s`. -/
private lemma eq_of_resolution {D : Type*} [Category D] {V V₁ V₂ U U₁ U₂ Z Z₀ : D}
    {A : V ⟶ V₁} {B : V₁ ⟶ V₂} {A' : U ⟶ U₁} {B' : U₁ ⟶ U₂} {α : V₂ ⟶ U₂} {α₁ : V₁ ⟶ U₁}
    {α₀ : V ⟶ U} {t : U₂ ⟶ Z} {t₀ : U ⟶ Z₀} {s : V₂ ⟶ Z} {s₀ : V ⟶ Z₀} {k : Z₀ ⟶ Z}
    (hB : B ≫ α = α₁ ≫ B') (hA : A ≫ α₁ = α₀ ≫ A') (ht : A' ≫ B' ≫ t = t₀ ≫ k)
    (hs : A ≫ B ≫ s = s₀ ≫ k) (h₀ : α₀ ≫ t₀ = s₀) (hm : Epi (A ≫ B)) : α ≫ t = s := by
  refine (cancel_epi (A ≫ B)).1 ?_
  rw [Category.assoc, reassoc_of% hB, reassoc_of% hA, ht, reassoc_of% h₀, ← hs,
    Category.assoc]

/-- The comparison of the two canonical derived tensor products intertwines their canonical
maps to the total tensor complex, on a pair of K-flat complexes. -/
theorem derivedTensorProductFunctorIsoSheafOfModules_hom_app_app_toTensor_of_kFlat
    (K L : CochainComplex (Modules X.O) ℤ)
    (hK : Stacks.SheafOfModules.KFlat.KFlat X.O K) (hL : Stacks.SheafOfModules.KFlat.KFlat X.O L) :
    ((derivedTensorProductFunctorIsoSheafOfModules X).hom.app (DerivedCategory.Q.obj K)).app
          (DerivedCategory.Q.obj L) ≫
        (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).toTensor K L =
      (canonicalDerivedTensorProduct X.O).toTensor K L := by
  have h₁ := Stacks.SheafOfModules.DerivedMonoidal.derivedBifunctorTensorIso_hom_app_app X.O
    (Stacks.SheafOfModules.DerivedTensorProduct.toRingedSiteDerivedTensorProduct
      (Stacks.SheafOfModules.canonicalDerivedTensorProduct X)) K L hK hL
  have h₂ := Stacks.SheafOfModules.DerivedMonoidal.derivedBifunctorTensorIso_hom_app_app X.O
    (canonicalDerivedTensorProduct X.O) K L hK hL
  have e₁ := (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).toTensor_eq_comparison K L
    hK hL
  have e₂ : (canonicalDerivedTensorProduct X.O).toTensor K L =
      ((canonicalDerivedTensorProduct X.O).comparison K L hK hL).hom := by
    rw [(canonicalDerivedTensorProduct X.O).toTensor_eq_comparisonRight K L hL,
      (canonicalDerivedTensorProduct X.O).comparisonRight_eq_comparison K L hK hL]
  have h₀ : ((derivedTensorProductFunctorIsoSheafOfModules X).hom.app
        (DerivedCategory.Q.obj K)).app (DerivedCategory.Q.obj L) =
      ((Stacks.SheafOfModules.DerivedMonoidal.canonicalTensorIso X.O).inv.app
          (DerivedCategory.Q.obj K)).app (DerivedCategory.Q.obj L) ≫
        ((Stacks.SheafOfModules.DerivedMonoidal.derivedBifunctorTensorIso X.O
          (Stacks.SheafOfModules.DerivedTensorProduct.toRingedSiteDerivedTensorProduct
            (Stacks.SheafOfModules.canonicalDerivedTensorProduct X))).hom.app
          (DerivedCategory.Q.obj K)).app (DerivedCategory.Q.obj L) := rfl
  rw [h₀, h₁, e₁, e₂]
  exact comp_comp_inv_comp_hom _ _ _ _ _
    (Iso.inv_hom_id_app_app (Stacks.SheafOfModules.DerivedMonoidal.canonicalTensorIso X.O) _ _)
    ((Iso.eq_comp_inv _).1 h₂)

/-- **The comparison of the two canonical derived tensor products intertwines their canonical
maps to the total tensor complex**, for arbitrary complexes `K` and `L`: the comparison
`derivedTensorProductFunctorIsoSheafOfModules` followed by the map `K ⊗ᴸ L ⟶ Tot(K ⊗ L)` of
`Stacks.SheafOfModules.canonicalDerivedTensorProduct` is the map of
`Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct`. -/
theorem derivedTensorProductFunctorIsoSheafOfModules_hom_app_app_toTensor
    (K L : CochainComplex (Modules X.O) ℤ) :
    ((derivedTensorProductFunctorIsoSheafOfModules X).hom.app (DerivedCategory.Q.obj K)).app
          (DerivedCategory.Q.obj L) ≫
        (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).toTensor K L =
      (canonicalDerivedTensorProduct X.O).toTensor K L := by
  obtain ⟨P, p, hP, hp⟩ := exists_kFlat_quasiIso X.O K
  obtain ⟨M, q, hM, hq⟩ := exists_kFlat_quasiIso X.O L
  have : IsIso (DerivedCategory.Q.map p) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ p).2 hp
  have : IsIso (DerivedCategory.Q.map q) := (DerivedCategory.isIso_Q_map_iff_quasiIso _ q).2 hq
  exact eq_of_resolution
    (((derivedTensorProductFunctorIsoSheafOfModules X).hom.app
      (DerivedCategory.Q.obj K)).naturality (DerivedCategory.Q.map q))
    (NatTrans.naturality_app (derivedTensorProductFunctorIsoSheafOfModules X).hom
      (DerivedCategory.Q.obj M) (DerivedCategory.Q.map p))
    ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).toTensor_naturality p q)
    ((canonicalDerivedTensorProduct X.O).toTensor_naturality p q)
    (derivedTensorProductFunctorIsoSheafOfModules_hom_app_app_toTensor_of_kFlat X P M hP hM)
    inferInstance

end Stacks.DerivedTensor.RingedSite

namespace Stacks.Duality.ProjectionFormulaLocallySmall

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.Cohomology.ProjectionFormulaPerfect.hasSheafifyOpens
  Stacks.Cohomology.ProjectionFormulaPerfect.wEqualsLocallyBijectiveOpens
attribute [local instance] Stacks.AssociatedSheaf.abelianModulesRingSheaf

/-- **On a scheme, the comparison of the two derived tensor products intertwines their
canonical maps to the total tensor complex**, at the standard model and for arbitrary
complexes `K`, `L` of `𝒪_Z`-modules. -/
theorem standardTensorIso_hom_app_app_toTensor (Z : AlgebraicGeometry.Scheme.{u})
    (K L : CochainComplex (Stacks.DerivedTensor.RingedSite.Modules Z.sheaf) ℤ) :
    ((standardTensorIso Z).hom.app (DerivedCategory.Q.obj K)).app (DerivedCategory.Q.obj L) ≫
        (Stacks.SheafOfModules.canonicalDerivedTensorProduct
          (Stacks.SheafOfModules.ringedSite Z.sheaf)).toTensor K L =
      (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct Z.sheaf).toTensor K L :=
  @Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctorIsoSheafOfModules_hom_app_app_toTensor
    (Stacks.SheafOfModules.ringedSite Z.sheaf) _ _ (HasDerivedCategory.standard _) _ _ _ K L

end Stacks.Duality.ProjectionFormulaLocallySmall

end
