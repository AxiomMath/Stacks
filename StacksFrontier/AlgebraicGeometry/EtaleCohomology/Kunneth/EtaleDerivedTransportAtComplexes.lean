module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperProjectionFormula.TorsionBaseChangeTransfer
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategorySquareQ
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperProjectionFormula.RingedBaseChangeComplex
public import StacksFrontier.CategoryTheory.Adjunction.TransportedAdjunctionConjugate

/-!
# The étale derived functors and their ringed-topos counterparts, at the class of a complex

For a commutative ring `Λ`, the derived categories `D(X_étale, Λ)` of sheaves of `Λ`-modules are
identified with the derived categories of the constant ringed topoi `(X_étale, Λ̲)` through
`Φ = Stacks.EtaleCohomology.etaleDerivedEquivalence`, induced by
`Θ = (etaleModulesEquivalence Λ X).functor`. Through `Φ` the derived inverse and direct images are
identified with the ringed-topos ones (`Stacks.EtaleCohomology.etaleRingedDerivedPullbackIso`,
`Stacks.EtaleCohomology.etaleDerivedPushforwardIso`). These identifications are lifted from the
homotopy category and carry no description of their components. This file computes them at the
class `Q K` of a complex: they are the underived comparisons applied degreewise, up to the
comparisons `Lg^* ⟶ g^*` of [Stacks, Tag 06YY] and the derived-functor units. It also identifies
the underived comparisons in the direction of `Θ` with the conjugates of those in the direction of
`Ψ = Θ⁻¹` used by `Stacks.EtaleCohomology.etaleModuleBaseChange_etaleRingedForget`, and so
transports that compatibility of the étale and ringed base change maps of sheaves of modules to the
direction of `Θ`.

## Main results

* `map_etaleDerivedEquivalenceFactorsIso_hom_comp_etaleRingedDerivedPullbackIso_hom` and
  `etaleRingedDerivedPullbackIso_inv_app_Q`: the inverse-image identification at `Q K`.
* `etaleDerivedEquivalenceFactorsIso_hom_comp_map_unit_comp_etaleDerivedPushforwardIso_hom`:
  the étale unit of `Rf_*`, read through `Φ`, is the ringed-topos unit after the underived
  comparison of direct images `Stacks.EtaleCohomology.etaleRingedPushforwardCompIso`.
* `Stacks.EtaleCohomology.etaleRingedPullbackIso_hom_app`,
  `Stacks.EtaleCohomology.etaleRingedPullbackCompIso_hom_app`,
  `Stacks.EtaleCohomology.etaleRingedPushforwardCompIso_hom_app`: the comparisons in the direction
  of `Θ` are the conjugates of those in the direction of `Ψ`.
* `Stacks.EtaleCohomology.etaleRingedPullbackCompIso_hom_app_comp_map_etaleModuleBaseChange`:
  `Θ` carries the étale base change map of sheaves of modules to the base change map of the
  square of constant ringed topoi.

## Implementation notes

The étale base change map is made an opaque variable before the transport lemma
`Stacks.CategoryTheory.TransportedAdjunction.conj_baseChange` is instantiated: written out, the
kernel unfolds it while comparing two spellings of the same categories.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackOfToposHom

-- `Stacks.EtaleCohomology.etaleDerivedEquivalence` and the derived images it identifies are built
-- for the standard model of the derived categories.
attribute [local instance] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat

universe u r

namespace Stacks.EtaleCohomology

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits
  etaleRingedPullbackOnHomotopy_hasLeftDerivedFunctor

variable (Λ : Type r) [CommRing Λ] {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The comparison of `Qh(q(Θ K))` with `Φ(Q K)`, written out. -/
theorem etaleDerivedEquivalenceFactorsIso_hom_app {Z : Scheme.{u}}
    (K : CochainComplex (EtaleModules.{u, r} Λ Z) ℤ) :
    (etaleDerivedEquivalenceFactorsIso.{u, r} Λ (X := Z)).hom.app K =
      (DerivedCategory.quotientCompQhIso _).hom.app
          (((etaleModulesEquivalence.{u, r} Λ Z).functor.mapHomologicalComplex
            (ComplexShape.up ℤ)).obj K) ≫
        (etaleModulesEquivalence.{u, r} Λ Z).functor.mapDerivedCategoryFactors.inv.app K :=
  rfl

/-- The chase behind
`map_etaleDerivedEquivalenceFactorsIso_hom_comp_etaleRingedDerivedPullbackIso_hom`, over
variables. -/
private theorem chase_pullbackIso {𝒞 : Type*} [Category* 𝒞] {a b c d e a' a'' : 𝒞}
    (x : a ⟶ b) (M₁ : b ⟶ c) (C₁ : c ⟶ d) (C₂ : d ⟶ e) (P : b ⟶ e) (hP : P = M₁ ≫ C₁ ≫ C₂)
    (M₂ : a ⟶ a') (y : a' ⟶ c) (h₁ : x ≫ M₁ = M₂ ≫ y) (cmp : a ⟶ a'') (fi : a'' ⟶ a')
    (h₂ : M₂ = cmp ≫ fi) (R : a'' ⟶ e) (h₃ : fi ≫ y ≫ C₁ ≫ C₂ = R) :
    x ≫ P = cmp ≫ R := by
  rw [hP, reassoc_of% h₁, h₂, Category.assoc, h₃]

/-- **The derived pullback along the morphism of constant ringed topoi is the étale derived
inverse image, at the class of a complex.** For a complex `K` of sheaves of `Λ`-modules on
`Y_étale`, the identification `Φ_Y ⋙ Lg^* ≅ g^{-1} ⋙ Φ_X` at `Q K`, read from the class of the
transported complex `Θ_Y K`, is the comparison `Lg^*(Θ_Y K) ⟶ g^*(Θ_Y K)` of [Stacks, Tag 06YY],
followed by the underived comparison `g^* Θ_Y ≅ Θ_X g^{-1}` applied degreewise. -/
theorem map_etaleDerivedEquivalenceFactorsIso_hom_comp_etaleRingedDerivedPullbackIso_hom
    (K : CochainComplex (EtaleModules.{u, r} Λ Y) ℤ) :
    (etaleRingedDerivedPullback.{u, r} Λ g).map
        ((etaleDerivedEquivalenceFactorsIso.{u, r} Λ (X := Y)).hom.app K) ≫
      (etaleRingedDerivedPullbackIso.{u, r} Λ g).hom.app (DerivedCategory.Q.obj K) =
      (derivedPullbackComparison (etaleRingedToposHom.{u, r} Λ g)).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
            (((etaleModulesEquivalence.{u, r} Λ Y).functor.mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K)) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          (Stacks.DerivedCategorySquare.degreewiseHom _ _ _ _
            (etaleRingedPullbackCompIso.{u, r} Λ g) K)) ≫
        (etaleDerivedEquivalenceFactorsIso.{u, r} Λ (X := X)).hom.app
          (((etaleModuleInverseImage.{u, r} Λ g).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        (etaleDerivedEquivalence.{u, r} Λ X).functor.map
          ((etaleModuleInverseImage.{u, r} Λ g).mapDerivedCategoryFactors.inv.app K) := by
  have : (etaleRingedPullback.{u, r} Λ g).mapDerivedCategory.IsLeftDerivedFunctor
      (etaleRingedPullback.{u, r} Λ g).mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso (EtaleRingedModules.{u, r} Λ Y) (ComplexShape.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts
      (HomotopyCategory.quasiIso (EtaleRingedModules.{u, r} Λ Y) (ComplexShape.up ℤ)) _
      (etaleRingedPullback.{u, r} Λ g).mapDerivedCategoryFactorsh
  have h2 := Functor.leftDerivedNatTrans_app (etaleRingedDerivedPullback.{u, r} Λ g)
    (etaleRingedPullback.{u, r} Λ g).mapDerivedCategory
    (derivedPullbackComparison (etaleRingedToposHom.{u, r} Λ g))
    (etaleRingedPullback.{u, r} Λ g).mapDerivedCategoryFactorsh.hom
    (HomotopyCategory.quasiIso (EtaleRingedModules.{u, r} Λ Y) (ComplexShape.up ℤ))
    (𝟙 _) ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
      (((etaleModulesEquivalence.{u, r} Λ Y).functor.mapHomologicalComplex
        (ComplexShape.up ℤ)).obj K))
  rw [NatTrans.id_app, Category.comp_id] at h2
  have h2' : (etaleRingedDerivedPullbackMapIso.{u, r} Λ g).hom.app (DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((etaleModulesEquivalence.{u, r} Λ Y).functor.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj K))) =
      (derivedPullbackComparison (etaleRingedToposHom.{u, r} Λ g)).app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
            (((etaleModulesEquivalence.{u, r} Λ Y).functor.mapHomologicalComplex
              (ComplexShape.up ℤ)).obj K)) ≫
        (etaleRingedPullback.{u, r} Λ g).mapDerivedCategoryFactorsh.inv.app _ := by
    rw [← h2, Category.assoc, Iso.hom_inv_id_app]
    exact (Category.comp_id _).symm
  have h3 := Stacks.DerivedCategorySquare.mapDerivedCategoryCompNatIso_trans_symm_hom_app_Q _ _ _ _
      (etaleRingedPullbackCompIso.{u, r} Λ g) K
  rw [← etaleDerivedEquivalenceFactorsIso_hom_app, ← Category.assoc
    ((DerivedCategory.quotientCompQhIso _).hom.app _),
    ← etaleDerivedEquivalenceFactorsIso_hom_app] at h3
  exact chase_pullbackIso _ _
    ((Dualizing.mapDerivedCategoryCompNatIso _ _ _
      (etaleRingedPullbackCompIso.{u, r} Λ g)).hom.app (DerivedCategory.Q.obj K))
    ((Dualizing.mapDerivedCategoryCompNatIso (etaleModuleInverseImage.{u, r} Λ g)
      (etaleModulesEquivalence.{u, r} Λ X).functor _ (Iso.refl _)).inv.app
        (DerivedCategory.Q.obj K)) _ rfl _ _
    ((etaleRingedDerivedPullbackMapIso.{u, r} Λ g).hom.naturality
      ((etaleDerivedEquivalenceFactorsIso.{u, r} Λ (X := Y)).hom.app K)) _ _ h2' _
    h3

/-- Solving `x ≫ P = c ≫ C ≫ F ≫ G` for the inverse of `P`, over variables. -/
private theorem eq_of_comp_eq_inverses {𝒞 : Type*} [Category* 𝒞] {a b e c₁ c₂ c₃ : 𝒞}
    (x : a ⟶ b) (P : b ⟶ e) (P' : e ⟶ b) (hP : P ≫ P' = 𝟙 _) (c : a ⟶ c₁) (C : c₁ ⟶ c₂)
    (F : c₂ ⟶ c₃) (G : c₃ ⟶ e) (c' : c₁ ⟶ a) (C' : c₂ ⟶ c₁) (F' : c₃ ⟶ c₂) (G' : e ⟶ c₃)
    (hc : c' ≫ c = 𝟙 _) (hC : C' ≫ C = 𝟙 _) (hF : F' ≫ F = 𝟙 _) (hG : G' ≫ G = 𝟙 _)
    (h : x ≫ P = c ≫ C ≫ F ≫ G) : P' = G' ≫ F' ≫ C' ≫ c' ≫ x := by
  have h₁ : G' ≫ F' ≫ C' ≫ c' ≫ c ≫ C ≫ F ≫ G = 𝟙 _ := by
    rw [reassoc_of% hc, reassoc_of% hC, reassoc_of% hF, hG]
  calc P' = (G' ≫ F' ≫ C' ≫ c' ≫ c ≫ C ≫ F ≫ G) ≫ P' := by rw [h₁, Category.id_comp]
    _ = G' ≫ F' ≫ C' ≫ c' ≫ x ≫ P ≫ P' := by rw [← h]; simp only [Category.assoc]
    _ = G' ≫ F' ≫ C' ≫ c' ≫ x := by rw [hP, Category.comp_id]

/-- **The inverse of the identification of the derived pullbacks, at the class of a complex.** -/
theorem etaleRingedDerivedPullbackIso_inv_app_Q (K : CochainComplex (EtaleModules.{u, r} Λ Y) ℤ) :
    (etaleRingedDerivedPullbackIso.{u, r} Λ g).inv.app (DerivedCategory.Q.obj K) =
      (etaleDerivedEquivalence.{u, r} Λ X).functor.map
          ((etaleModuleInverseImage.{u, r} Λ g).mapDerivedCategoryFactors.hom.app K) ≫
        (etaleDerivedEquivalenceFactorsIso.{u, r} Λ (X := X)).inv.app
          (((etaleModuleInverseImage.{u, r} Λ g).mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          (Stacks.DerivedCategorySquare.degreewiseInv _ _ _ _
            (etaleRingedPullbackCompIso.{u, r} Λ g) K)) ≫
        @CategoryTheory.inv _ _ _ _
          ((derivedPullbackComparison (etaleRingedToposHom.{u, r} Λ g)).app
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
              (((etaleModulesEquivalence.{u, r} Λ Y).functor.mapHomologicalComplex
                (ComplexShape.up ℤ)).obj K)))
          (isIso_etaleRingedDerivedPullbackComparison_app.{u, r} Λ g _) ≫
        (etaleRingedDerivedPullback.{u, r} Λ g).map
          ((etaleDerivedEquivalenceFactorsIso.{u, r} Λ (X := Y)).hom.app K) := by
  refine eq_of_comp_eq_inverses _ _ _ (Iso.hom_inv_id_app _ _) _ _ _ _ _ _ _ _
    (@IsIso.inv_hom_id _ _ _ _ _ (isIso_etaleRingedDerivedPullbackComparison_app.{u, r} Λ g _)) ?_
    (Iso.inv_hom_id_app _ _) ?_
    (map_etaleDerivedEquivalenceFactorsIso_hom_comp_etaleRingedDerivedPullbackIso_hom.{u, r} Λ g K)
  · exact Stacks.DerivedCategorySquare.map_comp_map_eq_id
      (HomotopyCategory.quotient _ (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      _ _ (Stacks.DerivedCategorySquare.degreewiseInv_comp_degreewiseHom _ _ _ _ _ K)
  · exact Stacks.DerivedCategorySquare.map_comp_map_eq_id _ _ _ (Iso.hom_inv_id_app _ _)

section Pushforward

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The chase behind
`etaleDerivedEquivalenceFactorsIso_hom_comp_map_etaleDerivedPushforwardComparisonIso_hom`, over
variables. -/
private theorem chase_pushforward {𝒟 ℛ : Type*} [Category* 𝒟] [Category* ℛ] (Fq : 𝒟 ⥤ ℛ)
    (Gq : ℛ ⥤ 𝒟) (ε : Gq ⋙ Fq ⟶ 𝟭 ℛ) {d₀ d₁ d₂ : 𝒟} {x₀ x₁ x₂ x₃ x₄ x₅ y : ℛ}
    (a₁ : x₀ ⟶ x₁) (a₂ : x₁ ⟶ Fq.obj d₀) (c₁ : d₀ ⟶ d₁) (c₂ : d₁ ⟶ d₂) (c₃ : d₂ ⟶ Gq.obj x₂)
    (r₁ : x₂ ⟶ x₃) (r₂ : x₃ ⟶ x₄) (r₃ : x₄ ⟶ x₅) (CI : d₀ ⟶ Gq.obj x₅)
    (hCI : CI = 𝟙 _ ≫ (c₁ ≫ (c₂ ≫ (c₃ ≫ Gq.map (r₁ ≫ (r₂ ≫ r₃))))))
    (c₃' : Gq.obj x₂ ⟶ d₂) (hc₃ : c₃ ≫ c₃' = 𝟙 _) (t : Fq.obj d₂ ⟶ y) (s : y ⟶ x₂)
    (hε : ε.app x₂ = Fq.map c₃' ≫ t ≫ s) (t' : Fq.obj d₀ ⟶ x₁) (Qx : x₁ ⟶ y)
    (hnat : Fq.map c₁ ≫ Fq.map c₂ ≫ t = t' ≫ Qx) (ha₂ : a₂ ≫ t' = 𝟙 _) (w : x₀ ⟶ x₃)
    (h₁ : a₁ ≫ Qx ≫ s ≫ r₁ = w) (R : x₀ ⟶ x₅) (h₃ : w ≫ r₂ ≫ r₃ = R) :
    (a₁ ≫ a₂) ≫ Fq.map CI ≫ ε.app x₅ = R := by
  have hn := ε.naturality (r₁ ≫ r₂ ≫ r₃)
  simp only [Functor.comp_map, Functor.id_map] at hn
  have h3 : Fq.map c₃ ≫ ε.app x₂ = t ≫ s := by
    rw [hε, ← Fq.map_comp_assoc, hc₃, CategoryTheory.Functor.map_id, Category.id_comp]
  rw [hCI]
  simp only [Fq.map_comp, Fq.map_id, Category.id_comp, Category.assoc, hn]
  rw [reassoc_of% h3, reassoc_of% hnat, reassoc_of% ha₂, reassoc_of% h₁, h₃]

/-- The underived comparison `f_* ⋙ Θ_Y ≅ Θ_X ⋙ f_*` of the étale direct image with the direct
image along the morphism of constant ringed topoi, read off
`Stacks.EtaleCohomology.etaleRingedPushforwardIso`. -/
def etaleRingedPushforwardCompIso :
    etaleModuleDirectImage.{u, r} Λ f ⋙ (etaleModulesEquivalence.{u, r} Λ Y).functor ≅
      (etaleModulesEquivalence.{u, r} Λ X).functor ⋙
        (etaleRingedToposHom.{u, r} Λ f).pushforwardModules :=
  Stacks.DerivedCategorySquare.transportedPushforwardIso (etaleModulesEquivalence.{u, r} Λ X)
    (etaleModulesEquivalence.{u, r} Λ Y) (etaleModuleDirectImage.{u, r} Λ f)
    (etaleRingedSiteHom.{u, r} Λ f).toRingedToposSiteHom.pushforwardTopos
    (etaleRingedToposHom.{u, r} Λ f).pushforwardModules (etaleRingedPushforwardIso.{u, r} Λ f)
    (etaleRingedSiteHom.{u, r} Λ f).pushforwardToposIso

private theorem comp_id_comp_eq {𝒞 : Type*} [Category* 𝒞] {a b c : 𝒞} (f : a ⟶ b) (g : b ⟶ c)
    (h : a ⟶ c) (e : f ≫ g = h) : f ≫ 𝟙 b ≫ g = h := by
  rw [Category.id_comp, e]

attribute [local instance] etaleRingedPushforwardTopos_additive
  etaleRingedToposHom_pushforwardModules_additive

/-- **The comparison of the étale and ringed-topos direct images on complexes, localized, is the
underived comparison applied degreewise.** -/
theorem etaleDerivedEquivalenceFactorsIso_hom_comp_map_etaleDerivedPushforwardComparisonIso_hom
    (M : CochainComplex (EtaleModules.{u, r} Λ X) ℤ) :
    (etaleDerivedEquivalenceFactorsIso.{u, r} Λ (X := Y)).hom.app
        (((etaleModuleDirectImage.{u, r} Λ f).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ≫
      (etaleDerivedEquivalence.{u, r} Λ Y).functor.map
        ((etaleDerivedPushforwardComparisonIso.{u, r} Λ f).hom.app M) ≫
      (etaleDerivedEquivalence.{u, r} Λ Y).counitIso.hom.app _ =
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
      (Stacks.DerivedCategorySquare.degreewiseHom _ _ _ _
        (etaleRingedPushforwardCompIso.{u, r} Λ f) M)) := by
  let Θc := (etaleModulesEquivalence.{u, r} Λ X).functor.mapHomologicalComplex (ComplexShape.up ℤ)
  let pT := (etaleRingedSiteHom.{u, r} Λ f).toRingedToposSiteHom.pushforwardTopos
  let x₁ := ((etaleModuleDirectImage.{u, r} Λ f).mapHomologicalComplex (ComplexShape.up ℤ)).map
    (((etaleModulesEquivalence.{u, r} Λ X).mapHomologicalComplex
      (ComplexShape.up ℤ)).unitIso.hom.app M)
  let x₂ := (NatIso.mapHomologicalComplex (etaleRingedPushforwardIso.{u, r} Λ f).symm
    (ComplexShape.up ℤ)).hom.app (Θc.obj M)
  let L := (pT.mapHomologicalComplex (ComplexShape.up ℤ)).obj (Θc.obj M)
  have hε :=
    Stacks.DerivedCategorySquare.mapDerivedCategoryEquivalenceOfEquivalence_counitIso_hom_app_Q
      (etaleModulesEquivalence.{u, r} Λ Y) L
  have hnat : (etaleDerivedEquivalence.{u, r} Λ Y).functor.map (DerivedCategory.Q.map x₁) ≫
      (etaleDerivedEquivalence.{u, r} Λ Y).functor.map (DerivedCategory.Q.map x₂) ≫
      (etaleModulesEquivalence.{u, r} Λ Y).functor.mapDerivedCategoryFactors.hom.app
        (((etaleModulesEquivalence.{u, r} Λ Y).inverse.mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L) =
      (etaleModulesEquivalence.{u, r} Λ Y).functor.mapDerivedCategoryFactors.hom.app
          (((etaleModuleDirectImage.{u, r} Λ f).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ≫
        DerivedCategory.Q.map (((etaleModulesEquivalence.{u, r} Λ Y).functor.mapHomologicalComplex
          (ComplexShape.up ℤ)).map (x₁ ≫ x₂)) := by
    refine Eq.trans ?_
      ((etaleModulesEquivalence.{u, r} Λ Y).functor.mapDerivedCategoryFactors_hom_naturality
        (x₁ ≫ x₂))
    simp only [Functor.map_comp, Category.assoc]
    rfl
  let εc := ((etaleModulesEquivalence.{u, r} Λ Y).mapHomologicalComplex
    (ComplexShape.up ℤ)).counitIso.hom.app L
  have h₁ : (DerivedCategory.quotientCompQhIso _).hom.app
        (((etaleModulesEquivalence.{u, r} Λ Y).functor.mapHomologicalComplex
            (ComplexShape.up ℤ)).obj
          (((etaleModuleDirectImage.{u, r} Λ f).mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) ≫
      DerivedCategory.Q.map (((etaleModulesEquivalence.{u, r} Λ Y).functor.mapHomologicalComplex
          (ComplexShape.up ℤ)).map (x₁ ≫ x₂)) ≫ DerivedCategory.Q.map εc ≫
      (DerivedCategory.quotientCompQhIso _).inv.app L =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        (((etaleModulesEquivalence.{u, r} Λ Y).functor.mapHomologicalComplex
          (ComplexShape.up ℤ)).map (x₁ ≫ x₂) ≫ εc)) := by
    refine Eq.trans ?_
      (Stacks.DerivedCategorySquare.quotientCompQhIso_hom_app_comp_Q_map_comp_inv_app
        (((etaleModulesEquivalence.{u, r} Λ Y).functor.mapHomologicalComplex
            (ComplexShape.up ℤ)).map (x₁ ≫ x₂) ≫ εc))
    simp only [Functor.map_comp, Category.assoc]
    rfl
  have hr₂ : DerivedCategory.Qh.map ((pT.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app
      (Θc.obj M)) = 𝟙 _ := by
    simp only [Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_inv]
    exact DerivedCategory.Qh.map_id _
  have hc : (((etaleModulesEquivalence.{u, r} Λ Y).functor.mapHomologicalComplex
      (ComplexShape.up ℤ)).map (x₁ ≫ x₂) ≫ εc) ≫
        (NatTrans.mapHomologicalComplex (etaleRingedSiteHom.{u, r} Λ f).pushforwardToposIso.inv
          (ComplexShape.up ℤ)).app (Θc.obj M) =
      Stacks.DerivedCategorySquare.degreewiseHom _ _ _ _
        (etaleRingedPushforwardCompIso.{u, r} Λ f) M := by
    ext n : 1
    simp [x₁, x₂, εc, etaleRingedPushforwardCompIso,
      Stacks.DerivedCategorySquare.transportedPushforwardIso_hom_app]
    rfl
  have h₃ : DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        (((etaleModulesEquivalence.{u, r} Λ Y).functor.mapHomologicalComplex
          (ComplexShape.up ℤ)).map (x₁ ≫ x₂) ≫ εc)) ≫
      DerivedCategory.Qh.map ((pT.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app
        (Θc.obj M)) ≫
      DerivedCategory.Qh.map ((etaleRingedSiteHom.{u, r} Λ f).pushforwardHomotopyToposIso.inv.app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (Θc.obj M))) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        (Stacks.DerivedCategorySquare.degreewiseHom _ _ _ _
          (etaleRingedPushforwardCompIso.{u, r} Λ f) M)) := by
    rw [hr₂]
    refine comp_id_comp_eq _ _ _ ?_
    show DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        (((etaleModulesEquivalence.{u, r} Λ Y).functor.mapHomologicalComplex
          (ComplexShape.up ℤ)).map (x₁ ≫ x₂) ≫ εc)) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (etaleRingedSiteHom.{u, r} Λ f).pushforwardToposIso.inv
          (ComplexShape.up ℤ)).app (Θc.obj M))) = _
    rw [← Functor.map_comp, ← Functor.map_comp, hc]
  exact chase_pushforward (etaleDerivedEquivalence.{u, r} Λ Y).functor
    (etaleDerivedEquivalence.{u, r} Λ Y).inverse (etaleDerivedEquivalence.{u, r} Λ Y).counitIso.hom
    _ _ (DerivedCategory.Q.map x₁) (DerivedCategory.Q.map x₂)
    ((etaleModulesEquivalence.{u, r} Λ Y).inverse.mapDerivedCategoryFactors.inv.app L)
    ((DerivedCategory.quotientCompQhIso _).inv.app L)
    (DerivedCategory.Qh.map ((pT.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app
        (Θc.obj M)))
    (DerivedCategory.Qh.map ((etaleRingedSiteHom.{u, r} Λ f).pushforwardHomotopyToposIso.inv.app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj (Θc.obj M))))
    _ rfl _ (Iso.inv_hom_id_app _ _) _ _ hε _ _ hnat (Iso.inv_hom_id_app _ _) _ h₁ _ h₃

private theorem chase_unit {𝒞 : Type*} [Category* 𝒞] {a₀ a₁ a₂ a₃ a₄ a₅ b : 𝒞} (a : a₀ ⟶ a₁)
    (y : a₁ ⟶ a₂) (z : a₂ ⟶ a₃) (p : a₁ ⟶ b) (e : b ⟶ a₄) (r : a₄ ⟶ a₅) (s : a₅ ⟶ a₃)
    (t : a₀ ⟶ a₄) (hA : y ≫ z = (p ≫ e) ≫ r ≫ s) (hE : a ≫ p ≫ e = t) :
    a ≫ y ≫ z = t ≫ r ≫ s := by
  rw [hA, Category.assoc, reassoc_of% hE]

/-- **The étale unit of `Rf_*`, read through the equivalences, is the ringed-topos unit after the
underived comparison of direct images.** -/
theorem etaleDerivedEquivalenceFactorsIso_hom_comp_map_unit_comp_etaleDerivedPushforwardIso_hom
    (M : CochainComplex (EtaleModules.{u, r} Λ X) ℤ) :
    (etaleDerivedEquivalenceFactorsIso.{u, r} Λ (X := Y)).hom.app
        (((etaleModuleDirectImage.{u, r} Λ f).mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ≫
      (etaleDerivedEquivalence.{u, r} Λ Y).functor.map
        ((etaleModuleDerivedDirectImageUnboundedUnit.{u, r} Λ f).app M) ≫
      (etaleDerivedPushforwardIso.{u, r} Λ f).hom.app (DerivedCategory.Q.obj M) =
    DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        (Stacks.DerivedCategorySquare.degreewiseHom _ _ _ _
          (etaleRingedPushforwardCompIso.{u, r} Λ f) M)) ≫
      (etaleRingedDerivedPushforwardUnit.{u, r} Λ f).app
        (((etaleModulesEquivalence.{u, r} Λ X).functor.mapHomologicalComplex
          (ComplexShape.up ℤ) ⋙ HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj M) ≫
      (etaleRingedDerivedPushforward.{u, r} Λ f).map
        ((etaleDerivedEquivalenceFactorsIso.{u, r} Λ (X := X)).hom.app M) :=
  chase_unit _ _ _ _ _ _ _ _
    (map_etaleModuleDerivedDirectImageUnboundedUnit_comp_etaleDerivedPushforwardIso.{u, r} Λ f M)
    (etaleDerivedEquivalenceFactorsIso_hom_comp_map_etaleDerivedPushforwardComparisonIso_hom.{u, r}
      Λ f M)

end Pushforward

section Conjugates

private theorem chase_comp_id {𝒞 : Type*} [Category* 𝒞] {a b c c' d : 𝒞} (p : a ⟶ b)
    (e : b ⟶ c) (e' : a ⟶ c') (q : c' ⟶ c) (t : c ⟶ d) (n : p ≫ e = e' ≫ q) :
    p ≫ e ≫ t ≫ 𝟙 d = e' ≫ q ≫ t := by
  rw [Category.comp_id, reassoc_of% n]

variable {X Y : Scheme.{u}} (g : X ⟶ Y)

/-- The identification of the ringed-topos direct image with the transported étale one is the
conjugate of the comparison `Stacks.EtaleCohomology.etaleRingedPushforwardComparison`. -/
theorem etaleRingedPushforwardModulesIso_hom_app
    (J : SheafOfModules.{max r (u + 1)} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
        (etaleRingedSite.{u, r} Λ X)).O)) :
    (etaleRingedPushforwardModulesIso.{u, r} Λ g).hom.app J =
      (etaleModulesEquivalence.{u, r} Λ Y).counitIso.inv.app
          ((etaleRingedToposHom.{u, r} Λ g).pushforwardModules.obj J) ≫
        (etaleModulesEquivalence.{u, r} Λ Y).functor.map
          ((etaleRingedPushforwardComparison.{u, r} Λ g).hom.app J) := by
  have n := (etaleModulesEquivalence.{u, r} Λ Y).counitIso.inv.naturality
    ((etaleRingedSiteHom.{u, r} Λ g).pushforwardToposIso.hom.app J)
  simp only [etaleRingedPushforwardModulesIso, etaleRingedPushforwardComparison, Iso.trans_hom,
    NatTrans.comp_app, Iso.symm_hom, Functor.isoWhiskerLeft_hom, Functor.isoWhiskerRight_hom,
    Functor.whiskerLeft_app, Functor.whiskerRight_app, Functor.rightUnitor_inv_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Functor.map_comp, Category.id_comp,
    Category.assoc] at n ⊢
  exact chase_comp_id _ _ _ _ _ n

/-- **The pullback of sheaves of `Λ̲`-modules is the étale inverse image, through the conjugate of
`Stacks.EtaleCohomology.etaleRingedPullbackComparison`.** -/
theorem etaleRingedPullbackIso_hom_app
    (I : SheafOfModules.{max r (u + 1)} (Stacks.SheafOfModules.Tensor.ringSheaf
      (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
        (etaleRingedSite.{u, r} Λ Y)).O)) :
    (etaleRingedPullbackIso.{u, r} Λ g).hom.app I =
      (etaleModulesEquivalence.{u, r} Λ X).counitIso.inv.app
          ((etaleRingedPullback.{u, r} Λ g).obj I) ≫
        (etaleModulesEquivalence.{u, r} Λ X).functor.map
          ((etaleRingedPullbackComparison.{u, r} Λ g).inv.app I) :=
  Stacks.CategoryTheory.TransportedAdjunction.leftAdjointUniq_hom_app_of_unit
    (etaleModulesEquivalence.{u, r} Λ Y) (etaleModulesEquivalence.{u, r} Λ X)
    (RingedToposHom.pullbackAdjPushforwardModules (etaleRingedToposHom.{u, r} Λ g))
    (etaleModuleInverseImageAdj.{u, r} Λ g) (etaleRingedPushforwardComparison.{u, r} Λ g)
    (etaleRingedPushforwardModulesIso.{u, r} Λ g) (etaleRingedPullbackComparison.{u, r} Λ g)
    (etaleRingedPushforwardModulesIso_hom_app.{u, r} Λ g)
    (unit_etaleRingedPullbackComparison.{u, r} Λ g) I

/-- The underived comparison `g^* Θ_Y ≅ Θ_X g^{-1}` is the conjugate of
`Stacks.EtaleCohomology.etaleRingedPullbackComparison`. -/
theorem etaleRingedPullbackCompIso_hom_app (N : EtaleModules.{u, r} Λ Y) :
    (etaleRingedPullbackCompIso.{u, r} Λ g).hom.app N =
      (etaleModulesEquivalence.{u, r} Λ X).counitIso.inv.app
          ((etaleRingedPullback.{u, r} Λ g).obj
            ((etaleModulesEquivalence.{u, r} Λ Y).functor.obj N)) ≫
        (etaleModulesEquivalence.{u, r} Λ X).functor.map
          ((etaleRingedPullbackComparison.{u, r} Λ g).inv.app
            ((etaleModulesEquivalence.{u, r} Λ Y).functor.obj N)) ≫
        (etaleModulesEquivalence.{u, r} Λ X).functor.map ((etaleModuleInverseImage.{u, r} Λ g).map
          ((etaleModulesEquivalence.{u, r} Λ Y).unitIso.inv.app N)) := by
  have h := etaleRingedPullbackIso_hom_app.{u, r} Λ g
    ((etaleModulesEquivalence.{u, r} Λ Y).functor.obj N)
  simp only [etaleRingedPullbackCompIso, Iso.trans_hom, NatTrans.comp_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Functor.associator_inv_app,
    Functor.isoWhiskerRight_hom, Functor.whiskerRight_app, Iso.symm_hom,
    Functor.leftUnitor_hom_app, Category.id_comp, Category.comp_id, Functor.comp_map]
  rw [h, Category.assoc]
  exact congrArg (fun t => _ ≫ _ ≫ t) (Category.comp_id _)

/-- The underived comparison `f_* Θ_X ≅ Θ_Y f_*` of direct images is the conjugate of
`Stacks.EtaleCohomology.etaleRingedPushforwardComparison`. -/
theorem etaleRingedPushforwardCompIso_hom_app (M : EtaleModules.{u, r} Λ X) :
    (etaleRingedPushforwardCompIso.{u, r} Λ g).hom.app M =
      (etaleModulesEquivalence.{u, r} Λ Y).functor.map ((etaleModuleDirectImage.{u, r} Λ g).map
          ((etaleModulesEquivalence.{u, r} Λ X).unitIso.hom.app M)) ≫
        (etaleModulesEquivalence.{u, r} Λ Y).functor.map
          ((etaleRingedPushforwardComparison.{u, r} Λ g).inv.app
            ((etaleModulesEquivalence.{u, r} Λ X).functor.obj M)) ≫
        (etaleModulesEquivalence.{u, r} Λ Y).counitIso.hom.app
          ((etaleRingedToposHom.{u, r} Λ g).pushforwardModules.obj
            ((etaleModulesEquivalence.{u, r} Λ X).functor.obj M)) := by
  have n := (etaleModulesEquivalence.{u, r} Λ Y).counitIso.hom.naturality
    ((etaleRingedSiteHom.{u, r} Λ g).pushforwardToposIso.inv.app
      ((etaleModulesEquivalence.{u, r} Λ X).functor.obj M))
  simp only [Functor.comp_map, Functor.id_map] at n
  rw [etaleRingedPushforwardCompIso, Stacks.DerivedCategorySquare.transportedPushforwardIso_hom_app]
  simp only [etaleRingedPushforwardComparison, Iso.trans_inv, NatTrans.comp_app,
    Functor.isoWhiskerRight_inv, Functor.whiskerRight_app, Functor.map_comp, Category.assoc]
  rw [n]

end Conjugates

section Square

variable {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (f' : X' ⟶ Y') (g' : X' ⟶ X)
  (w : g' ≫ f = f' ≫ g)

/-- **`Θ` carries the étale base change map to the base change map of the square of constant
ringed topoi**, through the comparisons `Stacks.EtaleCohomology.etaleRingedPullbackCompIso` and
`Stacks.EtaleCohomology.etaleRingedPushforwardCompIso`. -/
theorem etaleRingedPullbackCompIso_hom_app_comp_map_etaleModuleBaseChange
    (M : EtaleModules.{u, r} Λ X) :
    (etaleRingedPullbackCompIso.{u, r} Λ g).hom.app ((etaleModuleDirectImage.{u, r} Λ f).obj M) ≫
      (etaleModulesEquivalence.{u, r} Λ Y').functor.map
        ((etaleModuleBaseChange.{u, r} Λ f f' g g' w.symm).app M) ≫
      (etaleRingedPushforwardCompIso.{u, r} Λ f').hom.app
        ((etaleModuleInverseImage.{u, r} Λ g').obj M) =
    (etaleRingedPullback.{u, r} Λ g).map ((etaleRingedPushforwardCompIso.{u, r} Λ f).hom.app M) ≫
      (RingedToposHom.TwoIso.moduleBaseChange.{max r (u + 1)}
        (etaleRingedToposHomSquareTwoIso.{u, r} Λ f g f' g' w)).app
          ((etaleModulesEquivalence.{u, r} Λ X).functor.obj M) ≫
      (etaleRingedToposHom.{u, r} Λ f').pushforwardModules.map
        ((etaleRingedPullbackCompIso.{u, r} Λ g').hom.app M) := by
  have e : ∀ I : (SheafOfModules.{max r (u + 1)} (Stacks.SheafOfModules.Tensor.ringSheaf
        (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
          (etaleRingedSite.{u, r} Λ X)).O)),
      (RingedToposHom.TwoIso.moduleBaseChange.{max r (u + 1)}
        (etaleRingedToposHomSquareTwoIso.{u, r} Λ f g f' g' w)).app I =
      Stacks.CategoryTheory.BaseChange.map
        (RingedToposHom.pullbackAdjPushforwardModules (etaleRingedToposHom.{u, r} Λ f))
        (RingedToposHom.pullbackAdjPushforwardModules (etaleRingedToposHom.{u, r} Λ f'))
        (RingedToposHom.TwoIso.squarePullbackIso
          (X' := (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
            (etaleRingedSite.{u, r} Λ X')))
          (X := (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
            (etaleRingedSite.{u, r} Λ X)))
          (Y' := (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
            (etaleRingedSite.{u, r} Λ Y')))
          (Y := (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
            (etaleRingedSite.{u, r} Λ Y)))
          (etaleRingedToposHomSquareTwoIso.{u, r} Λ f g f' g' w)) (Iso.refl _) I := by
    intro I
    simp only [RingedToposHom.TwoIso.moduleBaseChange, Stacks.CategoryTheory.BaseChange.map,
      Stacks.CategoryTheory.BaseChange.twoSquare,
      Stacks.CategoryTheory.BaseChange.pullbackComparison, Iso.refl_inv, Category.comp_id]
  have hA := etaleModuleBaseChange_etaleRingedForget.{u, r} Λ f g f' g' w
  obtain ⟨β, hβ⟩ : ∃ β, β = etaleModuleBaseChange.{u, r} Λ f f' g g' w.symm := ⟨_, rfl⟩
  rw [← hβ] at hA ⊢
  have h := Stacks.CategoryTheory.TransportedAdjunction.conj_baseChange
    (RX := (SheafOfModules.{max r (u + 1)} (Stacks.SheafOfModules.Tensor.ringSheaf
        (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
          (etaleRingedSite.{u, r} Λ X)).O)))
    (RY := (SheafOfModules.{max r (u + 1)} (Stacks.SheafOfModules.Tensor.ringSheaf
        (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
          (etaleRingedSite.{u, r} Λ Y)).O)))
    (RX' := (SheafOfModules.{max r (u + 1)} (Stacks.SheafOfModules.Tensor.ringSheaf
        (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
          (etaleRingedSite.{u, r} Λ X')).O)))
    (RY' := (SheafOfModules.{max r (u + 1)} (Stacks.SheafOfModules.Tensor.ringSheaf
        (RingedSite.ringedTopos.{max r (u + 1), max r (u + 1), max r (u + 1)}
          (etaleRingedSite.{u, r} Λ Y')).O)))
    (etaleModulesEquivalence.{u, r} Λ X) (etaleModulesEquivalence.{u, r} Λ Y)
    (etaleModulesEquivalence.{u, r} Λ X') (etaleModulesEquivalence.{u, r} Λ Y')
    (etaleRingedPushforwardComparison.{u, r} Λ f) (etaleRingedPushforwardComparison.{u, r} Λ f')
    (etaleRingedPullbackComparison.{u, r} Λ g) (etaleRingedPullbackComparison.{u, r} Λ g')
    β (RingedToposHom.TwoIso.moduleBaseChange.{max r (u + 1)}
      (etaleRingedToposHomSquareTwoIso.{u, r} Λ f g f' g' w)) (fun I => by
        rw [e I]
        exact hA I) M
  refine Eq.trans ?_ (h.trans ?_)
  · rw [etaleRingedPullbackCompIso_hom_app, etaleRingedPushforwardCompIso_hom_app, Category.assoc]
  · rw [etaleRingedPushforwardCompIso_hom_app, etaleRingedPullbackCompIso_hom_app]

/-- `etaleRingedPullbackCompIso_hom_app_comp_map_etaleModuleBaseChange`, with the two pullback
comparisons moved to the other side. -/
theorem map_etaleModuleBaseChange_comp_etaleRingedPullbackCompIso_inv
    (M : EtaleModules.{u, r} Λ X) :
    (etaleModulesEquivalence.{u, r} Λ Y').functor.map
        ((etaleModuleBaseChange.{u, r} Λ f f' g g' w.symm).app M) ≫
      (etaleRingedPushforwardCompIso.{u, r} Λ f').hom.app
        ((etaleModuleInverseImage.{u, r} Λ g').obj M) ≫
      (etaleRingedToposHom.{u, r} Λ f').pushforwardModules.map
        ((etaleRingedPullbackCompIso.{u, r} Λ g').inv.app M) =
    (etaleRingedPullbackCompIso.{u, r} Λ g).inv.app ((etaleModuleDirectImage.{u, r} Λ f).obj M) ≫
      (etaleRingedPullback.{u, r} Λ g).map ((etaleRingedPushforwardCompIso.{u, r} Λ f).hom.app M) ≫
      (RingedToposHom.TwoIso.moduleBaseChange.{max r (u + 1)}
        (etaleRingedToposHomSquareTwoIso.{u, r} Λ f g f' g' w)).app
          ((etaleModulesEquivalence.{u, r} Λ X).functor.obj M) := by
  have h := etaleRingedPullbackCompIso_hom_app_comp_map_etaleModuleBaseChange.{u, r} Λ f g f' g' w M
  refine (Iso.cancel_iso_hom_left ((etaleRingedPullbackCompIso.{u, r} Λ g).app
    ((etaleModuleDirectImage.{u, r} Λ f).obj M)) _ _).1 ?_
  simp only [Iso.app_hom]
  rw [reassoc_of% h, Iso.hom_inv_id_app_assoc]
  rw [Stacks.DerivedCategorySquare.map_comp_map_eq_id
    (etaleRingedToposHom.{u, r} Λ f').pushforwardModules _ _ (Iso.hom_inv_id_app _ _)]
  exact congrArg (fun t => _ ≫ t) (Category.comp_id _)

end Square

end Stacks.EtaleCohomology
