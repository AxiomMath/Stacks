module

public import
  StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartSourceComparison.Mates

/-!
# Units along composites, the restriction model, and naturality of the derived sections

The unit of an adjunction along a composite,
`RingTheory.TorIndependence.unit_comp_map_restrictScalarsMerge`, the unit of the derived
change-of-rings adjunction read against the restriction model
(`AlgebraicGeometry.unit_comp_totalDerivedExtensionScalarsIsoRestrict`,
`AlgebraicGeometry.map_totalDerivedExtensionScalarsIsoRestrict_hom_comp_counit`), the naturality of
the localization of the derived sections over an affine open
(`AlgebraicGeometry.derivedStalkAffineSectionsIso_hom_naturality` and its variants),
`AlgebraicGeometry.derivedStalkAffineSectionsCongrIso_eq`, and some regroupings of composites.
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars (totalDerivedExtensionScalars
  totalDerivedExtensionScalarsComp totalDerivedExtensionScalarsComp_comparison
  derivedExtensionScalarsAdjunction)
open scoped TensorProduct ChangeOfRings

universe u w v₁ v₂ v₃ u₁ u₂ u₃

/-! ### The unit of an adjunction along a composite

The unit of a left adjoint written as a composite of two left adjoints, read against the unit of
the first factor. -/

section UnitComposite

variable {C₀ : Type u₁} [Category.{v₁} C₀] {C₁ : Type u₂} [Category.{v₂} C₁]
  {C₂ : Type u₃} [Category.{v₃} C₂]

/-- **A morphism into the image of the right adjoint, recovered from its adjunct.** The unit
followed by the right adjoint applied to the adjunct of `θ` is `θ`. -/
private theorem unit_comp_map_adjunct {L : C₀ ⥤ C₂} {R : C₂ ⥤ C₀} (adj : L ⊣ R) {Γ : C₀}
    {N : C₂} (θ : Γ ⟶ R.obj N) :
    adj.unit.app Γ ≫ R.map (L.map θ ≫ adj.counit.app N) = θ := by
  have h := adj.unit.naturality θ
  dsimp only [CategoryTheory.Functor.id_obj, CategoryTheory.Functor.id_map,
    CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.comp_map] at h
  rw [R.map_comp, ← Category.assoc, ← h, Category.assoc, adj.right_triangle_components,
    Category.comp_id]

/-- **The identification of two left adjoints of one functor, written out at an object.** The
comparison of `CategoryTheory.Adjunction.leftAdjointUniq` is the adjunct along the first
adjunction of the second adjunction's unit. -/
private theorem leftAdjointUniq_hom_app_eq {L₁ L₂ : C₀ ⥤ C₂} {R : C₂ ⥤ C₀} (adj₁ : L₁ ⊣ R)
    (adj₂ : L₂ ⊣ R) (X : C₀) :
    (Adjunction.leftAdjointUniq adj₁ adj₂).hom.app X =
      L₁.map (adj₂.unit.app X) ≫ adj₁.counit.app (L₂.obj X) := by
  refine (adj₁.homEquiv X _).injective ?_
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit,
    Adjunction.unit_leftAdjointUniq_hom_app]
  exact (unit_comp_map_adjunct adj₁ (adj₂.unit.app X)).symm

/-- A three-fold composite inside the argument of two nested functors, with the head split off
and the tail substituted. Every category, functor, object and morphism is a variable. -/
private theorem comp_map_map_subst {C₃ : Type u₁} [Category.{v₁} C₃] (G : C₃ ⥤ C₁) (F : C₁ ⥤ C₂)
    {X Y Z : C₃} {Z' : C₁} {W P T : C₂} (a : X ⟶ Y) (b : Y ⟶ Z) (c : G.obj Z ⟶ Z')
    (d : F.obj Z' ⟶ W) (p : F.obj (G.obj Y) ⟶ P) (q : P ⟶ W) (t : F.obj (G.obj X) ⟶ T)
    (v : T ⟶ P) (h : F.map (G.map b ≫ c) ≫ d = p ≫ q) (hn : F.map (G.map a) ≫ p = t ≫ v) :
    F.map (G.map (a ≫ b) ≫ c) ≫ d = t ≫ v ≫ q := by
  have e1 : G.map (a ≫ b) ≫ c = G.map a ≫ G.map b ≫ c := by
    rw [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [e1, CategoryTheory.Functor.map_comp, Category.assoc, h]
  simp only [← Category.assoc, hn]

/-- **The unit along a composite, applied to a morphism out of the first extension.** Let
`Eb ⊣ Rb` and `Ec ⊣ Rc` be adjunctions, let `Φinv : Ec ⟶ Eb ⋙ Ee` and let `cmp : Rb ⋙ Ec ≅ Ee`
satisfy `hstar`: `Φinv` is what the unit of the first adjunction becomes after `Ec` and `cmp`.

For a morphism `κ : Eb Γ ⟶ Re N`, the unit of the first adjunction followed by `κ` and the merge
`Ψ : Re ⋙ Rb ≅ Rc` is the unit of the composite adjunction followed by a morphism
`Ec Γ ⟶ N`, written out: `Φinv`, then `κ` extended, then `cmp` read backwards, then the merge
extended, then the counit. -/
private theorem unit_comp_map_comp_mergeIso {Eb : C₀ ⥤ C₁} {Rb : C₁ ⥤ C₀} {Ee : C₁ ⥤ C₂}
    {Re : C₂ ⥤ C₁} {Ec : C₀ ⥤ C₂} {Rc : C₂ ⥤ C₀} (adjb : Eb ⊣ Rb) (adjc : Ec ⊣ Rc)
    (Φinv : Ec ⟶ Eb ⋙ Ee) (cmp : Rb ⋙ Ec ≅ Ee) (Ψ : Re ⋙ Rb ≅ Rc)
    (hstar : ∀ W : C₀, Ec.map (adjb.unit.app W) ≫ cmp.hom.app (Eb.obj W) = Φinv.app W)
    (Γ : C₀) (N : C₂) (κ : Eb.obj Γ ⟶ Re.obj N) :
    adjb.unit.app Γ ≫ Rb.map κ ≫ Ψ.hom.app N =
      adjc.unit.app Γ ≫
        Rc.map (Φinv.app Γ ≫ Ee.map κ ≫ cmp.inv.app (Re.obj N) ≫
          Ec.map (Ψ.hom.app N) ≫ adjc.counit.app N) := by
  have hnat := cmp.hom.naturality κ
  dsimp only [CategoryTheory.Functor.comp_obj, CategoryTheory.Functor.comp_map] at hnat
  have h1 : Ec.map (adjb.unit.app Γ ≫ Rb.map κ) ≫ cmp.hom.app (Re.obj N) =
      Φinv.app Γ ≫ Ee.map κ := by
    rw [Ec.map_comp, Category.assoc, hnat, ← Category.assoc, hstar Γ]
  have h2 : Ec.map (adjb.unit.app Γ ≫ Rb.map κ) =
      Φinv.app Γ ≫ Ee.map κ ≫ cmp.inv.app (Re.obj N) := by
    rw [← Category.assoc, ← h1, Category.assoc, Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  have h3 : Ec.map (adjb.unit.app Γ ≫ Rb.map κ ≫ Ψ.hom.app N) ≫ adjc.counit.app N =
      Φinv.app Γ ≫ Ee.map κ ≫ cmp.inv.app (Re.obj N) ≫
        Ec.map (Ψ.hom.app N) ≫ adjc.counit.app N := by
    rw [← Category.assoc, Ec.map_comp, h2]
    simp only [Category.assoc]
  rw [← h3]
  exact (unit_comp_map_adjunct adjc (adjb.unit.app Γ ≫ Rb.map κ ≫ Ψ.hom.app N)).symm

end UnitComposite

namespace RingTheory.TorIndependence

/-! ### The unit along a composite of ring maps through a localization -/

section UnitLocalizationComposite

variable {A A₂ B : Type u} [CommRing A] [CommRing A₂] [CommRing B] [Algebra A A₂]
  (S : Submonoid A) [IsLocalization S A₂] (e : A₂ →+* B)
  [HasDerivedCategory.{u} (ModuleCat.{u} A)] [HasDerivedCategory.{u} (ModuleCat.{u} A₂)]
  [HasDerivedCategory.{u} (ModuleCat.{u} B)]

include S in
/-- **The unit of the derived change-of-rings adjunction along `e ∘ (A → A₂)`, against the unit
along `A → A₂`.** For `A₂` a localization of `A`, `e` a ring map out of it, a complex `Γ` over
`A`, a complex `N` over `B` and a morphism `κ : Γ ⊗ᴸ_A A₂ ⟶ N|_{A₂}`: the unit along `A → A₂`
followed by `κ` restricted and the merge `Ψ` of the two restrictions of scalars is the unit along
`e ∘ (A → A₂)` followed by an explicit morphism `Γ ⊗ᴸ_A B ⟶ N`.

That morphism is the composition isomorphism of derived extension of scalars read backwards,
then `κ` extended along `e`, then
`RingTheory.TorIndependence.restrictScalarsDerivedExtendCompIso` read backwards, then the merge
extended and the counit. -/
public theorem unit_comp_map_restrictScalarsMerge
    (Ψ : (ModuleCat.restrictScalars.{u} e).mapDerivedCategory ⋙
          (ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategory ≅
        (ModuleCat.restrictScalars.{u} (e.comp (algebraMap A A₂))).mapDerivedCategory)
    (Γ : DerivedCategory (ModuleCat.{u} A)) (N : DerivedCategory (ModuleCat.{u} B))
    (κ : (totalDerivedExtensionScalars.{u, u, u} (algebraMap A A₂)).functor.obj Γ ⟶
      (ModuleCat.restrictScalars.{u} e).mapDerivedCategory.obj N) :
    (derivedExtendRestrictAdjunction (A := A) (A₂ := A₂)).unit.app Γ ≫
        (ModuleCat.restrictScalars.{u} (algebraMap A A₂)).mapDerivedCategory.map κ ≫
          Ψ.hom.app N =
      (@derivedExtensionScalarsAdjunction.{u, u, u, u, u} A B _ _ (e.comp (algebraMap A A₂)) _ _
            (totalDerivedExtensionScalars.{u, u, u} (e.comp (algebraMap A A₂))).functor
            (totalDerivedExtensionScalars.{u, u, u} (e.comp (algebraMap A A₂))).comparison
            (totalDerivedExtensionScalars.{u, u, u}
              (e.comp (algebraMap A A₂))).isLeftDerived).unit.app Γ ≫
        (ModuleCat.restrictScalars.{u} (e.comp (algebraMap A A₂))).mapDerivedCategory.map
          ((totalDerivedExtensionScalarsComp.{u, u} (algebraMap A A₂) e).inv.app Γ ≫
            (totalDerivedExtensionScalars.{u, u, u} e).functor.map κ ≫
              (restrictScalarsDerivedExtendCompIso.{u, u} S e).inv.app
                  ((ModuleCat.restrictScalars.{u} e).mapDerivedCategory.obj N) ≫
                (totalDerivedExtensionScalars.{u, u, u} (e.comp (algebraMap A A₂))).functor.map
                    (Ψ.hom.app N) ≫
                  (@derivedExtensionScalarsAdjunction.{u, u, u, u, u} A B _ _
                    (e.comp (algebraMap A A₂)) _ _
                    (totalDerivedExtensionScalars.{u, u, u} (e.comp (algebraMap A A₂))).functor
                    (totalDerivedExtensionScalars.{u, u, u}
                      (e.comp (algebraMap A A₂))).comparison
                    (totalDerivedExtensionScalars.{u, u, u}
                      (e.comp (algebraMap A A₂))).isLeftDerived).counit.app N) :=
  unit_comp_map_comp_mergeIso (derivedExtendRestrictAdjunction (A := A) (A₂ := A₂))
    (@derivedExtensionScalarsAdjunction.{u, u, u, u, u} A B _ _ (e.comp (algebraMap A A₂)) _ _
      (totalDerivedExtensionScalars.{u, u, u} (e.comp (algebraMap A A₂))).functor
      (totalDerivedExtensionScalars.{u, u, u} (e.comp (algebraMap A A₂))).comparison
      (totalDerivedExtensionScalars.{u, u, u} (e.comp (algebraMap A A₂))).isLeftDerived)
    (totalDerivedExtensionScalarsComp.{u, u} (algebraMap A A₂) e).inv
    (restrictScalarsDerivedExtendCompIso.{u, u} S e) Ψ
    (fun W => map_unit_comp_restrictScalarsDerivedExtendCompIso_hom_app S e W) Γ N κ

end UnitLocalizationComposite

end RingTheory.TorIndependence

namespace AlgebraicGeometry

/-! ### The unit of the derived change-of-rings adjunction, read against the restriction model -/

section UnitRestrict

/-- **The unit of the derived change-of-rings adjunction, read against
`AlgebraicGeometry.totalDerivedExtensionScalarsIsoRestrict`.** For `ε` an isomorphism of rings
with inverse `ε'`, the unit of the adjunction of Stacks 0GMT along `ε`, followed by derived
restriction of scalars along `ε` applied to the identification of derived extension of scalars
along `ε` with derived restriction of scalars along `ε'`, is the unit of the derived transport
adjunction of that restriction equivalence. -/
public theorem unit_comp_totalDerivedExtensionScalarsIsoRestrict {R R₂ : Type u} [CommRing R]
    [CommRing R₂] (ε : R →+* R₂) (ε' : R₂ →+* R) (h₁ : ∀ x, ε' (ε x) = x)
    (h₂ : ∀ z, ε (ε' z) = z) (W : DerivedCategory (ModuleCat.{u} R)) :
    (@derivedExtensionScalarsAdjunction.{u, u, u, u, u} R R₂ _ _ ε _ _
          (totalDerivedExtensionScalars.{u, u, u} ε).functor
          (totalDerivedExtensionScalars.{u, u, u} ε).comparison
          (totalDerivedExtensionScalars.{u, u, u} ε).isLeftDerived).unit.app W ≫
        (ModuleCat.restrictScalars.{u, u, u} ε).mapDerivedCategory.map
          ((totalDerivedExtensionScalarsIsoRestrict.{u, u} ε ε' h₁ h₂).hom.app W) =
      (Adjunction.mapDerivedCategory
        (StacksDraft.DerivedRingIso.adjRestrictScalarsOfInv.{u} ε ε' h₁ h₂)).unit.app W :=
  Adjunction.unit_leftAdjointUniq_hom_app _ _ W

/-- **The concrete transport unit is an isomorphism.** The unit of the derived transport
adjunction of the restriction equivalence attached to an invertible ring homomorphism is
invertible, its left adjoint — derived restriction of scalars along `ε'` — being an equivalence
and hence fully faithful. -/
public theorem isIso_unit_mapDerivedCategory_adjRestrictScalarsOfInv {R R₂ : Type u} [CommRing R]
    [CommRing R₂] (ε : R →+* R₂) (ε' : R₂ →+* R) (h₁ : ∀ x, ε' (ε x) = x)
    (h₂ : ∀ z, ε (ε' z) = z) :
    IsIso (Adjunction.mapDerivedCategory
      (StacksDraft.DerivedRingIso.adjRestrictScalarsOfInv.{u} ε ε' h₁ h₂)).unit := by
  let : (ModuleCat.restrictScalars.{u, u, u} ε').mapDerivedCategory.IsEquivalence :=
    Stacks.DerivedQCoh.isEquivalence_mapDerivedCategory
      (ModuleCat.restrictScalarsEquivalenceOfRingEquiv
        ({ ε' with invFun := ε, left_inv := h₂, right_inv := h₁ } : R₂ ≃+* R))
  infer_instance

/-- **The unit read against the restriction model is an isomorphism**: the composite of
`AlgebraicGeometry.unit_comp_totalDerivedExtensionScalarsIsoRestrict` is invertible. -/
public theorem isIso_unit_comp_totalDerivedExtensionScalarsIsoRestrict {R R₂ : Type u}
    [CommRing R] [CommRing R₂] (ε : R →+* R₂) (ε' : R₂ →+* R) (h₁ : ∀ x, ε' (ε x) = x)
    (h₂ : ∀ z, ε (ε' z) = z) (W : DerivedCategory (ModuleCat.{u} R)) :
    IsIso ((@derivedExtensionScalarsAdjunction.{u, u, u, u, u} R R₂ _ _ ε _ _
            (totalDerivedExtensionScalars.{u, u, u} ε).functor
            (totalDerivedExtensionScalars.{u, u, u} ε).comparison
            (totalDerivedExtensionScalars.{u, u, u} ε).isLeftDerived).unit.app W ≫
          (ModuleCat.restrictScalars.{u, u, u} ε).mapDerivedCategory.map
            ((totalDerivedExtensionScalarsIsoRestrict.{u, u} ε ε' h₁ h₂).hom.app W)) := by
  rw [unit_comp_totalDerivedExtensionScalarsIsoRestrict ε ε' h₁ h₂ W]
  have := isIso_unit_mapDerivedCategory_adjRestrictScalarsOfInv.{u} ε ε' h₁ h₂
  infer_instance

/-- **The counit form of the restriction model of derived extension of scalars along an
isomorphism.** For `ε` invertible with inverse `ε'`, derived extension along `ε'` applied to
`AlgebraicGeometry.totalDerivedExtensionScalarsIsoRestrict`, followed by the counit along `ε'`,
is the composition isomorphism of derived extension of scalars followed by the extension along
`ε' ∘ ε` of `ζ` and the counit along `ε' ∘ ε`.

The statement takes as hypothesis `hζ`: the unit of the derived transport adjunction of the
restriction-of-scalars equivalence attached to `ε` is the canonical identification `ζ` of the
identity functor with restriction along `ε' ∘ ε`, read against the merge `Ψ` of the two
restrictions. -/
public theorem map_totalDerivedExtensionScalarsIsoRestrict_hom_comp_counit {R R₂ : Type u}
    [CommRing R] [CommRing R₂] [HasDerivedCategory.{u} (ModuleCat.{u} R)]
    [HasDerivedCategory.{u} (ModuleCat.{u} R₂)]
    (ε : R →+* R₂) (ε' : R₂ →+* R) (h₁ : ∀ x, ε' (ε x) = x) (h₂ : ∀ z, ε (ε' z) = z)
    (Ψ : (ModuleCat.restrictScalars.{u} ε').mapDerivedCategory ⋙
          (ModuleCat.restrictScalars.{u} ε).mapDerivedCategory ≅
        (ModuleCat.restrictScalars.{u} (ε'.comp ε)).mapDerivedCategory)
    (hΨ : Ψ = RingTheory.TorIndependence.mapDerivedCategoryCompNatIso
      (ModuleCat.restrictScalars.{u} ε') (ModuleCat.restrictScalars.{u} ε)
      (ModuleCat.restrictScalars.{u} (ε'.comp ε))
      (ModuleCat.restrictScalarsComp'.{u} ε ε' (ε'.comp ε) rfl).symm)
    (ζ : 𝟭 (DerivedCategory (ModuleCat.{u} R)) ⟶
      (ModuleCat.restrictScalars.{u} (ε'.comp ε)).mapDerivedCategory)
    (hζ : ∀ M, (Adjunction.mapDerivedCategory
          (StacksDraft.DerivedRingIso.adjRestrictScalarsOfInv.{u} ε ε' h₁ h₂)).unit.app M =
        ζ.app M ≫ Ψ.inv.app M)
    (M : DerivedCategory (ModuleCat.{u} R)) :
    (totalDerivedExtensionScalars.{u, u, u} ε').functor.map
          ((totalDerivedExtensionScalarsIsoRestrict.{u, u} ε ε' h₁ h₂).hom.app M) ≫
        (@derivedExtensionScalarsAdjunction.{u, u, u, u, u} R₂ R _ _ ε' _ _
          (totalDerivedExtensionScalars.{u, u, u} ε').functor
          (totalDerivedExtensionScalars.{u, u, u} ε').comparison
          (totalDerivedExtensionScalars.{u, u, u} ε').isLeftDerived).counit.app M =
      (totalDerivedExtensionScalarsComp.{u, u} ε ε').hom.app M ≫
        (totalDerivedExtensionScalars.{u, u, u} (ε'.comp ε)).functor.map (ζ.app M) ≫
          (@derivedExtensionScalarsAdjunction.{u, u, u, u, u} R R _ _ (ε'.comp ε) _ _
            (totalDerivedExtensionScalars.{u, u, u} (ε'.comp ε)).functor
            (totalDerivedExtensionScalars.{u, u, u} (ε'.comp ε)).comparison
            (totalDerivedExtensionScalars.{u, u, u} (ε'.comp ε)).isLeftDerived).counit.app M := by
  have hIR : (totalDerivedExtensionScalarsIsoRestrict.{u, u} ε ε' h₁ h₂).hom.app M =
      (totalDerivedExtensionScalars.{u, u, u} ε).functor.map
          ((Adjunction.mapDerivedCategory
            (StacksDraft.DerivedRingIso.adjRestrictScalarsOfInv.{u} ε ε' h₁ h₂)).unit.app M) ≫
        (@derivedExtensionScalarsAdjunction.{u, u, u, u, u} R R₂ _ _ ε _ _
          (totalDerivedExtensionScalars.{u, u, u} ε).functor
          (totalDerivedExtensionScalars.{u, u, u} ε).comparison
          (totalDerivedExtensionScalars.{u, u, u} ε).isLeftDerived).counit.app
          ((ModuleCat.restrictScalars.{u} ε').mapDerivedCategory.obj M) :=
    leftAdjointUniq_hom_app_eq _ _ M
  have hmate := RingTheory.TorIndependence.totalDerivedExtensionScalarsComp_hom_app_comp_counit
    ε ε' Ψ hΨ M
  have hnat := (totalDerivedExtensionScalarsComp.{u, u} ε ε').hom.naturality (ζ.app M)
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj] at hnat
  rw [hIR, hζ M]
  exact comp_map_map_subst (totalDerivedExtensionScalars.{u, u, u} ε).functor
    (totalDerivedExtensionScalars.{u, u, u} ε').functor (ζ.app M) (Ψ.inv.app M) _ _ _ _ _ _
    hmate.symm hnat

end UnitRestrict

/-! ### The localization of the derived sections, natural in the complex -/

section Naturality

variable {A : CommRingCat.{u}} {X : Scheme.{u}} (i : Spec A ⟶ X)
  (K₁ K₂ : DerivedCategory X.Modules)
  (hK₁ : ∀ m : ℤ, ((DerivedCategory.homologyFunctor X.Modules m).obj K₁).IsQuasicoherent)
  (hK₂ : ∀ m : ℤ, ((DerivedCategory.homologyFunctor X.Modules m).obj K₂).IsQuasicoherent)
  (ψ : K₁ ⟶ K₂)

/-- **`AlgebraicGeometry.tildeDerivedSectionsIso` is natural in the complex.** -/
public theorem tildeDerivedSectionsIso_hom_naturality :
    (tilde.functor A).mapDerivedCategory.map ((affineDerivedSections i).map ψ) ≫
        (tildeDerivedSectionsIso i K₂ hK₂).hom =
      (tildeDerivedSectionsIso i K₁ hK₁).hom ≫ (Stacks.Duality.derivedPullback i).map ψ := by
  have hd : ∀ (L : DerivedCategory X.Modules)
      (hL : ∀ m : ℤ, ((DerivedCategory.homologyFunctor X.Modules m).obj L).IsQuasicoherent),
      (tildeDerivedSectionsIso i L hL).hom =
        ((derivedTildeCompι A).app ((affineDerivedSections i).obj L)).inv ≫
          (derivedTildeGlobalSectionsAdjunction A).val.counit.app
            ((Stacks.Duality.derivedPullback i).obj L) := fun _ _ => rfl
  have h1 := (derivedTildeCompι A).inv.naturality ((affineDerivedSections i).map ψ)
  have h2 := (derivedTildeGlobalSectionsAdjunction A).val.counit.naturality
    ((Stacks.Duality.derivedPullback i).map ψ)
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.id_map, Functor.id_obj] at h1 h2
  rw [hd, hd]
  dsimp only [Iso.app_inv, Functor.comp_map, Functor.comp_obj]
  rw [← Category.assoc, h1, Category.assoc, h2]
  simp only [Category.assoc]

/-- **`AlgebraicGeometry.derivedStalkAffineSectionsIso` is natural in the complex.** -/
public theorem derivedStalkAffineSectionsIso_hom_naturality (y : Spec A) :
    (totalDerivedExtensionScalars.{u, u, u} (specGermRingHom A y)).functor.map
          ((affineDerivedSections i).map ψ) ≫
        (derivedStalkAffineSectionsIso i y K₂ hK₂).hom =
      (derivedStalkAffineSectionsIso i y K₁ hK₁).hom ≫
        (totalDerivedExtensionScalars.{u, u, u} (i.stalkMap y).hom).functor.map
          ((derivedStalkFunctor (i y)).map ψ) := by
  have hd : ∀ (L : DerivedCategory X.Modules)
      (hL : ∀ m : ℤ, ((DerivedCategory.homologyFunctor X.Modules m).obj L).IsQuasicoherent),
      (derivedStalkAffineSectionsIso i y L hL).hom =
        (derivedTildeStalkIso A y).hom.app ((affineDerivedSections i).obj L) ≫
          (derivedStalkFunctor y).map (tildeDerivedSectionsIso i L hL).hom ≫
            (derivedPullbackStalkIso i y).hom.app L := fun _ _ => rfl
  have h1 := (derivedTildeStalkIso A y).hom.naturality ((affineDerivedSections i).map ψ)
  have h2 := tildeDerivedSectionsIso_hom_naturality i K₁ K₂ hK₁ hK₂ ψ
  have h3 := (derivedPullbackStalkIso i y).hom.naturality ψ
  dsimp only [Functor.comp_map, Functor.comp_obj] at h1 h2 h3
  have h2' := congrArg (derivedStalkFunctor y).map h2
  simp only [CategoryTheory.Functor.map_comp] at h2'
  rw [hd, hd]
  dsimp only [Iso.app_hom, Functor.comp_map, Functor.comp_obj]
  rw [← Category.assoc, h1, Category.assoc]
  simp only [Category.assoc]
  refine congrArg (fun z => (derivedTildeStalkIso A y).hom.app
    ((affineDerivedSections i).obj K₁) ≫ z) ?_
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (fun z => z ≫ (derivedPullbackStalkIso i y).hom.app K₂) h2').trans
      ((Category.assoc _ _ _).trans
        ((congrArg (fun z => (derivedStalkFunctor y).map
            (tildeDerivedSectionsIso i K₁ hK₁).hom ≫ z) h3).trans
          (Category.assoc _ _ _).symm)))

/-- **`AlgebraicGeometry.derivedStalkAffineSectionsRestrictIso` is natural in the complex.** -/
public theorem derivedStalkAffineSectionsRestrictIso_hom_naturality (y : Spec A)
    (ε' : (Spec A).presheaf.stalk y →+* X.presheaf.stalk (i y))
    (h₁ : ∀ x, ε' ((i.stalkMap y).hom x) = x)
    (h₂ : ∀ z, (i.stalkMap y).hom (ε' z) = z) :
    (totalDerivedExtensionScalars.{u, u, u} (specGermRingHom A y)).functor.map
          ((affineDerivedSections i).map ψ) ≫
        (derivedStalkAffineSectionsRestrictIso i y K₂ hK₂ ε' h₁ h₂).hom =
      (derivedStalkAffineSectionsRestrictIso i y K₁ hK₁ ε' h₁ h₂).hom ≫
        (ModuleCat.restrictScalars.{u, u, u} ε').mapDerivedCategory.map
          ((derivedStalkFunctor (i y)).map ψ) := by
  have he : (derivedStalkAffineSectionsRestrictIso i y K₂ hK₂ ε' h₁ h₂).hom =
      (derivedStalkAffineSectionsIso i y K₂ hK₂).hom ≫
        (totalDerivedExtensionScalarsIsoRestrict (i.stalkMap y).hom ε' h₁ h₂).hom.app
          ((derivedStalkFunctor (i y)).obj K₂) := rfl
  rw [he, ← Category.assoc,
    derivedStalkAffineSectionsIso_hom_naturality i K₁ K₂ hK₁ hK₂ ψ y, Category.assoc]
  exact derivedStalkAffineSectionsIso_hom_comp_map i y K₁ hK₁ ε' h₁ h₂
    ((derivedStalkFunctor (i y)).map ψ)

end Naturality

/-! ### The target corner with the point of `X` left free -/

section CongrSpelling

/-- Replacing the ring homomorphism inside
`AlgebraicGeometry.totalDerivedExtensionScalarsIsoRestrict` by an equal one: the isomorphism is
unchanged apart from the transport of its source. -/
private theorem totalDerivedExtensionScalarsIsoRestrict_congr {R R₂ : Type u} [CommRing R]
    [CommRing R₂] [HasDerivedCategory.{w} (ModuleCat.{u} R)]
    [HasDerivedCategory.{w} (ModuleCat.{u} R₂)] (σ σ' : R →+* R₂) (hσ : σ = σ') (ε : R₂ →+* R)
    (h₁ : ∀ x, ε (σ x) = x) (h₂ : ∀ v, σ (ε v) = v)
    (h₁' : ∀ x, ε (σ' x) = x) (h₂' : ∀ v, σ' (ε v) = v)
    (M : DerivedCategory (ModuleCat.{u} R)) :
    (totalDerivedExtensionScalarsIsoRestrict σ ε h₁ h₂).app M =
      eqToIso (congrArg
          (fun r : R →+* R₂ => (totalDerivedExtensionScalars.{u, u, u} r).functor.obj M) hσ) ≪≫
        (totalDerivedExtensionScalarsIsoRestrict σ' ε h₁' h₂').app M := by
  subst hσ
  exact (Iso.refl_trans _).symm

variable {A : CommRingCat.{u}} {X : Scheme.{u}}

/-- The germ localization of the derived stalk of `K` at `i w` is the germ localization of the
derived stalk at any point `z = i w`, read along the specialization isomorphism. -/
public theorem derivedStalkAffineSections_extend_obj_eq (i : Spec A ⟶ X) (w : Spec A) (z : X)
    (hz : z = i w) (K : DerivedCategory X.Modules) :
    (totalDerivedExtensionScalars.{u, u, u} (i.stalkMap w).hom).functor.obj
        ((derivedStalkFunctor (i w)).obj K) =
      (totalDerivedExtensionScalars.{u, u, u}
          ((X.presheaf.stalkCongr (.of_eq hz)).hom ≫ i.stalkMap w).hom).functor.obj
        ((derivedStalkFunctor z).obj K) := by
  subst hz
  exact congrArg (fun r => (totalDerivedExtensionScalars.{u, u, u} r).functor.obj
    ((derivedStalkFunctor (i w)).obj K)) (by simp)

/-- **`AlgebraicGeometry.derivedStalkAffineSectionsCongrIso`, with the point of `X` left free.**
It is `AlgebraicGeometry.derivedStalkAffineSectionsIso` — whose target is the derived stalk at
`i w` *extended* along the germ comparison — followed by the replacement of that extension of
scalars by restriction of scalars along the given inverse `ε`, both read at the point `z` through
the specialization isomorphism. -/
public theorem derivedStalkAffineSectionsCongrIso_eq (i : Spec A ⟶ X) [IsOpenImmersion i]
    (w : Spec A) (z : X) (hz : z = i w) (K : DerivedCategory X.Modules)
    (hK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj K).IsQuasicoherent)
    (ε : ToType ((Spec A).presheaf.stalk w) →+* ToType (X.presheaf.stalk z))
    (k₁ : ∀ t, ε (((X.presheaf.stalkCongr (.of_eq hz)).hom ≫ i.stalkMap w).hom t) = t)
    (k₂ : ∀ v, ((X.presheaf.stalkCongr (.of_eq hz)).hom ≫ i.stalkMap w).hom (ε v) = v) :
    derivedStalkAffineSectionsCongrIso i w z hz K hK ε k₁ k₂ =
      derivedStalkAffineSectionsIso i w K hK ≪≫
        eqToIso (derivedStalkAffineSections_extend_obj_eq i w z hz K) ≪≫
          (totalDerivedExtensionScalarsIsoRestrict
              ((X.presheaf.stalkCongr (.of_eq hz)).hom ≫ i.stalkMap w).hom ε k₁ k₂).app
            ((derivedStalkFunctor z).obj K) := by
  subst hz
  refine Eq.trans (derivedStalkAffineSectionsRestrictIso_eq i w K hK ε
    (fun t => by simpa using k₁ t) (fun v => by simpa using k₂ v)) ?_
  exact congrArg (fun t => derivedStalkAffineSectionsIso i w K hK ≪≫ t)
    (totalDerivedExtensionScalarsIsoRestrict_congr (i.stalkMap w).hom
      ((X.presheaf.stalkCongr (.of_eq (rfl : i w = i w))).hom ≫ i.stalkMap w).hom (by simp) ε
      (fun t => by simpa using k₁ t) (fun v => by simpa using k₂ v) k₁ k₂
      ((derivedStalkFunctor (i w)).obj K))

end CongrSpelling

/-! ### Three regroupings and one adjoint transposition -/

section Transpose

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]

/-- **A square in the middle of a four-fold composite, with the first two factors merged.**  Two
morphisms under `F`, then a component of `β : F ⟶ G`, then a morphism out of `G`: the first two
are merged and replaced by `hab`, `β` is carried across by naturality, and what is left is
closed by `h2`. -/
public theorem map_map_natTrans_comp {F G : C ⥤ D} (β : F ⟶ G) {X Y Y' Z : C} {W V : D}
    (a : X ⟶ Y) (b : Y ⟶ Z) (a' : X ⟶ Y') (b' : Y' ⟶ Z) (hab : a ≫ b = a' ≫ b')
    (d : G.obj Z ⟶ W) (s₂ : G.obj X ⟶ V) (s₃ : V ⟶ W)
    (h2 : G.map (a' ≫ b') ≫ d = s₂ ≫ s₃) :
    F.map a ≫ F.map b ≫ β.app Z ≫ d = β.app X ≫ s₂ ≫ s₃ := by
  rw [← CategoryTheory.Functor.map_comp_assoc, hab, ← Category.assoc, β.naturality,
    Category.assoc, h2]

/-- **The last factor inside a seven-fold composite under a functor, cancelled against its
inverse outside.** -/
public theorem comp_map_comp7_cancel (F : C ⥤ D) {X₀ X₁ X₂ X₃ X₄ X₅ X₆ X₇ : C} {W₀ W₁ : D}
    (p : W₀ ⟶ F.obj X₀) (r₁ : X₀ ⟶ X₁) (r₂ : X₁ ⟶ X₂) (r₃ : X₂ ⟶ X₃) (r₄ : X₃ ⟶ X₄)
    (r₅ : X₄ ⟶ X₅) (r₆ : X₅ ⟶ X₆) (t : X₆ ⟶ X₇) (t' : X₇ ⟶ X₆) (ht : t ≫ t' = 𝟙 X₆)
    (q : F.obj X₆ ⟶ W₁) :
    (p ≫ F.map (r₁ ≫ r₂ ≫ r₃ ≫ r₄ ≫ r₅ ≫ r₆ ≫ t)) ≫ (F.map t' ≫ q) =
      p ≫ F.map (r₁ ≫ r₂ ≫ r₃ ≫ r₄ ≫ r₅ ≫ r₆) ≫ q := by
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]
  rw [← Category.assoc (F.map t) (F.map t') q, ← CategoryTheory.Functor.map_comp, ht,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- **The tail of a composite under a functor, replaced.** -/
public theorem comp_map_subst_tail (F : C ⥤ D) {X₀ X₁ X₂ X₆ : C} {W₀ W₁ : D}
    (p : W₀ ⟶ F.obj X₀) (r₁ : X₀ ⟶ X₁) (r₂ : X₁ ⟶ X₂) {z z' : X₂ ⟶ X₆}
    (h : z = z') (q : F.obj X₆ ⟶ W₁) :
    p ≫ F.map (r₁ ≫ r₂ ≫ z) ≫ q = p ≫ F.map (r₁ ≫ r₂ ≫ z') ≫ q :=
  congrArg (fun w => p ≫ F.map (r₁ ≫ r₂ ≫ w) ≫ q) h

/-- Two inverse pairs, nested, cancel. -/
public theorem comp4_cancel_mid {A B C' : D} (u : A ⟶ B) (u' : B ⟶ A)
    (v : B ⟶ C') (v' : C' ⟶ B) (hu : u' ≫ u = 𝟙 B) (hv : v' ≫ v = 𝟙 C') :
    (v' ≫ u') ≫ (u ≫ v) = 𝟙 C' := by
  rw [Category.assoc, ← Category.assoc u' u v, hu, Category.id_comp, hv]

/-- **The adjoint transposition of an equation whose left-hand side is a unit.** If the unit at
`Γ`, followed by the right adjoint applied to `inner` and then by an invertible `q`, is to be
`rhs`, it suffices that `inner` be the transpose of `rhs ≫ q⁻¹` — the left adjoint applied to it
followed by the counit. -/
public theorem unit_comp_map_comp_eq {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R) {Γ Z : C} {V : D}
    (inner : L.obj Γ ⟶ V) (q : R.obj V ⟶ Z) (q' : Z ⟶ R.obj V) (hq : q' ≫ q = 𝟙 Z)
    (rhs : Γ ⟶ Z) (h : inner = L.map (rhs ≫ q') ≫ adj.counit.app V) :
    adj.unit.app Γ ≫ R.map inner ≫ q = rhs := by
  subst h
  rw [← Category.assoc, unit_comp_map_adjunct adj, Category.assoc, hq, Category.comp_id]

end Transpose

end AlgebraicGeometry

end
