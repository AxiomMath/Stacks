module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.Composition
public import StacksFrontier.CategoryTheory.Adjunction.LiftedConjugate
public import StacksFrontier.CategoryTheory.Adjunction.UniqueCompTranspose
public import StacksFrontier.CategoryTheory.Localization.MapHomotopyCategoryAdjunctionCounit

/-!
# Restriction and derived pullback along an open immersion, by uniqueness of adjoints

For an open immersion `j : U ⟶ X`, restriction `j^*` and derived pullback `Lj^*` are both left
adjoint to `Rj_*` on `D(𝒪_X)`, hence isomorphic by uniqueness of adjoints. Read on the class of a
complex through the structure maps of the two functors, this isomorphism is the degreewise
identification of restriction with pullback. The isomorphism on `D_QCoh` used for `f^!` is its
restriction.

## Main results

* `Stacks.Duality.derivedRestrictAdjointIso`: `j^* ≅ Lj^*` on `D(𝒪_X)`.
* `Stacks.Duality.derivedRestrictAdjointIso_inv_app_Qh`: its value on the homotopy category.
* `Stacks.Duality.restrictedDerivedRestrictAdjointIso_hom_app_hom`: the `D_QCoh` version is its
  restriction.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace CategoryTheory.ObjectProperty

/-- The unit of an adjunction restricted to full subcategories along its lifts. -/
theorem restrictFullyFaithful_lift_unit_app_hom {C₁ C₂ : Type*} [Category C₁] [Category C₂]
    {P₁ : ObjectProperty C₁} {P₂ : ObjectProperty C₂} {L : C₁ ⥤ C₂} {R : C₂ ⥤ C₁} (adj : L ⊣ R)
    (hL : ∀ X : P₁.FullSubcategory, P₂ ((P₁.ι ⋙ L).obj X))
    (hR : ∀ Y : P₂.FullSubcategory, P₁ ((P₂.ι ⋙ R).obj Y)) (X : P₁.FullSubcategory) :
    ((adj.restrictFullyFaithful P₁.fullyFaithfulι P₂.fullyFaithfulι
      (P₂.liftCompιIso _ hL).symm (P₁.liftCompιIso _ hR).symm).unit.app X).hom =
      adj.unit.app X.obj := by
  have h := Adjunction.map_restrictFullyFaithful_unit_app adj P₁.fullyFaithfulι
    P₂.fullyFaithfulι (P₂.liftCompιIso _ hL).symm (P₁.liftCompιIso _ hR).symm X
  exact h.trans (by simp [liftCompιIso])

end CategoryTheory.ObjectProperty

namespace Stacks.Duality

variable {U X : Scheme.{u}} (j : U ⟶ X) [IsOpenImmersion j]

/-- The two left adjoints of `Rj_*` on the unbounded derived categories, at the locally small
model. -/
def derivedRestrictAdjointIso : OpenImmersion.derivedRestrict j ≅ derivedPullback j :=
  (OpenImmersion.derivedRestrictPushforwardAdjunction j).leftAdjointUniq (derivedAdjunction j)

/-- The chase behind `derivedRestrictAdjointIso_inv_app_Qh`. -/
theorem derivedRestrictAdjointIso_chase {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (G : 𝒟 ⥤ 𝒞)
    {x z zP : 𝒞} {px rx q₁ q₂ : 𝒟} (a : x ⟶ G.obj px) (uR : x ⟶ G.obj rx) (ι : px ⟶ rx)
    (f : rx ⟶ q₂) (α : px ⟶ q₁) (m' : q₁ ⟶ q₂) (ηR : x ⟶ z) (ηP : x ⟶ zP) (pm : zP ⟶ z)
    (βR βR' : z ⟶ G.obj q₂) (βP : zP ⟶ G.obj q₁) (H1 : a ≫ G.map ι = uR)
    (H2 : uR ≫ G.map f = ηR ≫ βR) (H3 : a ≫ G.map α = ηP ≫ βP)
    (H4 : βP ≫ G.map m' = pm ≫ βR') (hβ : βR' = βR) (H5 : ηR = ηP ≫ pm) :
    a ≫ G.map (ι ≫ f) = a ≫ G.map (α ≫ m') := by
  rw [G.map_comp, G.map_comp, reassoc_of% H1, H2, reassoc_of% H3, H4, hβ, H5, Category.assoc]

/-- `u ≫ 𝟙 ≫ G.map 𝟙 = u`. -/
theorem comp_id_comp_map_id {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] (G : 𝒟 ⥤ 𝒞) {a : 𝒞}
    {y : 𝒟} (u : a ⟶ G.obj y) : u ≫ 𝟙 (G.obj y) ≫ G.map (𝟙 y) = u := by
  simp

/-- Two left adjoints `F, F'` of `G`, on the homotopy categories: the unit of `F` is that of
`F'` followed by `G` of the comparison `F' ≅ F`. -/
theorem homotopyAdjunction_unit_app_quotient_leftAdjointUniq {𝒜 ℬ : Type*} [Category 𝒜]
    [Abelian 𝒜] [Category ℬ] [Abelian ℬ] {F F' : 𝒜 ⥤ ℬ} {G : ℬ ⥤ 𝒜} [F.Additive]
    [F'.Additive] [G.Additive] (adj : F ⊣ G) (adj' : F' ⊣ G) (M : CochainComplex 𝒜 ℤ) :
    (Stacks.SmallDerivedCategory.homotopyAdjunction adj).unit.app
        ((HomotopyCategory.quotient _ _).obj M) =
      (Adjunction.mapHomotopyCategoryAdjunction adj' (ComplexShape.up ℤ)).unit.app
          ((HomotopyCategory.quotient _ _).obj M) ≫
        (G.mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((Stacks.Homology.mapHomotopyCategoryIso (adj.leftAdjointUniq adj').symm
            (ComplexShape.up ℤ)).hom.app ((HomotopyCategory.quotient _ _).obj M)) := by
  rw [Stacks.SmallDerivedCategory.homotopyAdjunction_unit_app_quotient,
    Adjunction.mapHomotopyCategoryAdjunction_unit_app_quotient]
  simp only [Functor.mapHomotopyCategoryFactors, Stacks.Homology.mapHomotopyCategoryIso,
    Quotient.lift.isLift_inv, Iso.symm_hom]
  have key : (HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).map
      ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).unit.app M) =
      (HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).map
        ((adj'.mapHomologicalComplexAdjunction (ComplexShape.up ℤ)).unit.app M ≫
          (G.mapHomologicalComplex _).map ((NatTrans.mapHomologicalComplex
            (adj.leftAdjointUniq adj').inv (ComplexShape.up ℤ)).app M)) := by
    congr 1
    ext n
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      NatTrans.mapHomologicalComplex_app_f, Adjunction.leftAdjointUniq_inv_app]
    dsimp [Adjunction.mapHomologicalComplex, Adjunction.mapHomologicalComplexAdjunction]
    exact (Adjunction.unit_leftAdjointUniq_hom_app adj' adj (M.X n)).symm
  exact (comp_id_comp_map_id (G.mapHomotopyCategory (ComplexShape.up ℤ)) _).trans
    (key.trans (Functor.map_comp _ _ _))


/-- **Restriction ≅ derived pullback by uniqueness of adjoints, on the homotopy category**: read
through the structure maps, it is the degreewise identification of restriction with pullback. -/
theorem derivedRestrictAdjointIso_inv_app_Qh (K : HomotopyCategory X.Modules (ComplexShape.up ℤ)) :
    (derivedRestrictAdjointIso j).inv.app (DerivedCategory.Qh.obj K) ≫
      (Scheme.Modules.restrictFunctor j).mapDerivedCategoryFactorsh.hom.app K =
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison
        j.toLRSHom.toShHom).app K ≫
      DerivedCategory.Qh.map ((Stacks.Homology.mapHomotopyCategoryIso
        (Scheme.Modules.restrictFunctorIsoPullback j).symm (ComplexShape.up ℤ)).hom.app K) := by
  obtain ⟨M, rfl⟩ : ∃ M, (HomotopyCategory.quotient _ _).obj M = K := ⟨K.as, rfl⟩
  refine Adjunction.eq_of_unit_comp_map_eq (derivedAdjunction j) ?_
  have H1 := Adjunction.unit_leftAdjointUniq_hom_app (derivedAdjunction j)
    (OpenImmersion.derivedRestrictPushforwardAdjunction j)
    (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj M))
  rw [← Adjunction.leftAdjointUniq_inv_app] at H1
  have H2 := Stacks.SmallDerivedCategory.derivedAdjunction_unit_app_Qh
    (Scheme.Modules.restrictAdjunction j) (Iso.refl _)
    ((Stacks.Duality.homotopyPushforward j).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso U.Modules (ComplexShape.up ℤ)))
    (AlgebraicGeometry.Scheme.Modules.exists_quasiIso_isKInjective U)
    ((HomotopyCategory.quotient _ _).obj M)
  have hf : (Stacks.SmallDerivedCategory.leftDerivedFactorsQh (Iso.refl
      (Scheme.Modules.restrictFunctor j).mapDerivedCategory)).hom.app
        ((HomotopyCategory.quotient _ _).obj M) =
      (Scheme.Modules.restrictFunctor j).mapDerivedCategoryFactorsh.hom.app
        ((HomotopyCategory.quotient _ _).obj M) := by
    simp [Stacks.SmallDerivedCategory.leftDerivedFactorsQh]
  rw [hf] at H2
  have H3 := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedAdjunction_unit_fac
    j.toLRSHom.toShHom ((HomotopyCategory.quotient _ _).obj M)
  have H4 := (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardUnit
    j.toLRSHom.toShHom).naturality ((Stacks.Homology.mapHomotopyCategoryIso
        (Scheme.Modules.restrictFunctorIsoPullback j).symm (ComplexShape.up ℤ)).hom.app
          ((HomotopyCategory.quotient _ _).obj M))
  have hβ : (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardUnit
      j.toLRSHom.toShHom).app (((Scheme.Modules.restrictFunctor j).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj M)) =
      ((Stacks.Duality.homotopyPushforward j).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso U.Modules (ComplexShape.up ℤ))).app
        (((Scheme.Modules.restrictFunctor j).mapHomotopyCategory
        (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj M)) := rfl
  have H3' : (derivedAdjunction j).unit.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj M)) ≫
      (Stacks.Duality.derivedPushforward j).map
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison
          j.toLRSHom.toShHom).app ((HomotopyCategory.quotient _ _).obj M)) = _ := H3
  have H4' : (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardUnit
      j.toLRSHom.toShHom).app _ ≫ (Stacks.Duality.derivedPushforward j).map
        (DerivedCategory.Qh.map ((Stacks.Homology.mapHomotopyCategoryIso
        (Scheme.Modules.restrictFunctorIsoPullback j).symm (ComplexShape.up ℤ)).hom.app
          ((HomotopyCategory.quotient _ _).obj M))) = _ := H4.symm
  have H5 : DerivedCategory.Qh.map
      ((Stacks.SmallDerivedCategory.homotopyAdjunction
        (Scheme.Modules.restrictAdjunction j)).unit.app
        ((HomotopyCategory.quotient _ _).obj M)) =
      DerivedCategory.Qh.map
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.homotopyPullbackPushforwardAdjunction
          j.toLRSHom.toShHom).unit.app ((HomotopyCategory.quotient _ _).obj M)) ≫
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pushforwardToDerivedCategory
          j.toLRSHom.toShHom).map ((Stacks.Homology.mapHomotopyCategoryIso
            (Scheme.Modules.restrictFunctorIsoPullback j).symm (ComplexShape.up ℤ)).hom.app
              ((HomotopyCategory.quotient _ _).obj M)) :=
    (congrArg DerivedCategory.Qh.map (homotopyAdjunction_unit_app_quotient_leftAdjointUniq
      (Scheme.Modules.restrictAdjunction j)
      (Scheme.Modules.pullbackPushforwardAdjunction j) M)).trans
      (DerivedCategory.Qh.map_comp _ _)
  exact derivedRestrictAdjointIso_chase (Stacks.Duality.derivedPushforward j)
    ((derivedAdjunction j).unit.app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj M)))
    ((OpenImmersion.derivedRestrictPushforwardAdjunction j).unit.app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj M)))
    ((derivedRestrictAdjointIso j).inv.app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj M)))
    ((Scheme.Modules.restrictFunctor j).mapDerivedCategoryFactorsh.hom.app
      ((HomotopyCategory.quotient _ _).obj M))
    ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison
        j.toLRSHom.toShHom).app ((HomotopyCategory.quotient _ _).obj M))
    (DerivedCategory.Qh.map ((Stacks.Homology.mapHomotopyCategoryIso
        (Scheme.Modules.restrictFunctorIsoPullback j).symm (ComplexShape.up ℤ)).hom.app
          ((HomotopyCategory.quotient _ _).obj M)))
    (DerivedCategory.Qh.map
      ((Stacks.SmallDerivedCategory.homotopyAdjunction
        (Scheme.Modules.restrictAdjunction j)).unit.app
        ((HomotopyCategory.quotient _ _).obj M)))
    (DerivedCategory.Qh.map
        ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.homotopyPullbackPushforwardAdjunction
          j.toLRSHom.toShHom).unit.app ((HomotopyCategory.quotient _ _).obj M)))
    ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.pushforwardToDerivedCategory
          j.toLRSHom.toShHom).map ((Stacks.Homology.mapHomotopyCategoryIso
            (Scheme.Modules.restrictFunctorIsoPullback j).symm (ComplexShape.up ℤ)).hom.app
              ((HomotopyCategory.quotient _ _).obj M)))
    _ _ _ H1 H2 H3' H4' hβ H5

/-- The isomorphism of `D_QCoh` is the ambient one. -/
theorem restrictedDerivedRestrictAdjointIso_hom_app_hom [CompactSpace U] [QuasiSeparatedSpace U]
    [CompactSpace X] [QuasiSeparatedSpace X] (K : quasiCoherentDerivedCategory X) :
    ((restrictedDerivedRestrictAdjointIso j).hom.app K).hom =
      (derivedRestrictAdjointIso j).hom.app K.obj := by
  refine Adjunction.eq_of_unit_comp_map_eq (OpenImmersion.derivedRestrictPushforwardAdjunction j) ?_
  have h := congrArg InducedCategory.Hom.hom
    (Adjunction.unit_leftAdjointUniq_hom_app
      (OpenImmersion.quasiCoherentDerivedRestrictAdjunction j
        (OpenImmersion.isQuasicoherent_homology_derivedRestrict j)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs j))
      (quasiCoherentDerivedAdjunction j (isQuasicoherent_homology_derivedPullback' j)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs j)) K)
  rw [ObjectProperty.FullSubcategory.comp_hom] at h
  erw [ObjectProperty.restrictFullyFaithful_lift_unit_app_hom,
    ObjectProperty.restrictFullyFaithful_lift_unit_app_hom] at h
  exact h.trans (Adjunction.unit_leftAdjointUniq_hom_app
    (OpenImmersion.derivedRestrictPushforwardAdjunction j) (derivedAdjunction j) K.obj).symm

/-- The `D_QCoh` comparison `j^* ≅ Lj^*` is the ambient one, on inverses. -/
theorem restrictedDerivedRestrictAdjointIso_inv_app_hom [CompactSpace U] [QuasiSeparatedSpace U]
    [CompactSpace X] [QuasiSeparatedSpace X] (K : quasiCoherentDerivedCategory X) :
    ((restrictedDerivedRestrictAdjointIso j).inv.app K).hom =
      (derivedRestrictAdjointIso j).inv.app K.obj := by
  rw [← cancel_epi ((derivedRestrictAdjointIso j).hom.app K.obj), Iso.hom_inv_id_app,
    ← restrictedDerivedRestrictAdjointIso_hom_app_hom, ← ObjectProperty.FullSubcategory.comp_hom,
    Iso.hom_inv_id_app]
  rfl

end Stacks.Duality
