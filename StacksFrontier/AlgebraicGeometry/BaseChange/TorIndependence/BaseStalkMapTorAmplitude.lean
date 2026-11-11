module

public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekRelativeTorDimension
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffinePointwiseRingChange
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.StalkCohomologyMap
public import StacksFrontier.Algebra.Category.ModuleCat.ExtendScalarsBaseRing
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.PerfectMorphism.AffineLocal

/-!
# Finite Tor dimension of the base stalk map of a restricted square

Let `g : S' ⟶ S` be a morphism of schemes whose stalk maps `𝒪_{S, g(s')} ⟶ 𝒪_{S', s'}` have
finite Tor dimension. For a commutative square `Y → X₂ → S₂ ← S₂'` whose base `S₂' ⟶ S₂` lies over
`g` through open immersions `S₂ ⟶ S` and `S₂' ⟶ S'`, the base stalk map of
`AlgebraicGeometry.baseStalkMap` at any point of `Y` again has finite Tor dimension: up to the
isomorphisms of stalks along the two open immersions it is a stalk map of `g`.

This is the input on Tor amplitude that the pointwise base-change map of Stacks 0DJ7 consumes on
the squares of spectra of the charts of a base-change square.

## Main results

* `AlgebraicGeometry.exists_hasTorAmplitudeCanonical_of_bijective`: finite Tor dimension of a ring
  map transports along isomorphisms of its source and target.
* `AlgebraicGeometry.exists_hasTorAmplitudeCanonical_baseStalkMap`: the base stalk map of a
  square lying over `g` through open immersions has finite Tor dimension.
* `AlgebraicGeometry.hasFiniteTorDimensionRingHom_of_isLocalization`: finite Tor dimension of a ring
  map passes to its localizations.
* `AlgebraicGeometry.hasFiniteTorDimensionRingHom_stalkMap_of_appLE`: finite Tor dimension of the
  ring maps of `g` on affine opens passes to its stalk maps.

## References

* [Stacks Project, Tag 0DJ7](https://stacks.math.columbia.edu/tag/0DJ7)
* [Stacks Project, Tag 066E](https://stacks.math.columbia.edu/tag/066E)
-/

@[expose] public noncomputable section

open CategoryTheory StacksDraft.TorAmplitude

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

/-- **Finite Tor dimension transports along isomorphisms of rings.** If `φ₁ : R₁ → S₁` has finite
Tor dimension and `τ : R₁ ≅ R₂`, `σ : S₁ ≅ S₂` are ring isomorphisms with `σ ∘ φ₁ = φ₂ ∘ τ`, then
`S₂` has Tor amplitude in some interval over `R₂` through `φ₂`. -/
theorem exists_hasTorAmplitudeCanonical_of_bijective {R₁ S₁ R₂ S₂ : Type u} [CommRing R₁]
    [CommRing S₁] [CommRing R₂] [CommRing S₂] (φ₁ : R₁ →+* S₁) (φ₂ : R₂ →+* S₂)
    (τ : R₁ →+* R₂) (hτ : Function.Bijective τ) (σ : S₁ →+* S₂) (hσ : Function.Bijective σ)
    (hcomm : σ.comp φ₁ = φ₂.comp τ) (h : HasFiniteTorDimensionRingHom φ₁) :
    ∃ a b : ℤ, HasTorAmplitudeCanonical R₂
      ((DerivedCategory.singleFunctor (ModuleCat.{u} R₂) 0).obj
        ((ModuleCat.restrictScalars φ₂).obj (ModuleCat.of S₂ S₂))) a b := by
  obtain ⟨a, b, hab⟩ := h
  let M := (CochainComplex.singleFunctor (ModuleCat.{u} S₁) 0).obj (ModuleCat.of S₁ S₁)
  have h₁ : HasTorAmplitudeCanonical R₁
      (DerivedCategory.Q.obj ((CochainComplex.restrictScalars φ₁).obj M)) a b :=
    BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso
      (DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex
        (ModuleCat.restrictScalars φ₁) (ComplexShape.up ℤ) 0).app (ModuleCat.of S₁ S₁)).symm)
      a b hab
  let : Algebra S₁ S₂ := σ.toAlgebra
  let : Algebra R₁ R₂ := τ.toAlgebra
  have h₂ := Stacks.Duality.hasTorAmplitudeCanonical_restrictScalars_extendScalars_of_isLocalization
    φ₁ σ τ φ₂ hcomm ⊥ (RingTheory.TorIndependence.isLocalization_bot_of_bijective hσ) ⊥
    (RingTheory.TorIndependence.isLocalization_bot_of_bijective hτ) M a b h₁
  refine ⟨a, b, BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso ?_ a b h₂⟩
  exact DerivedCategory.Q.mapIso ((CochainComplex.restrictScalars φ₂).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex (ModuleCat.extendScalars σ)
          (ComplexShape.up ℤ) 0).app (ModuleCat.of S₁ S₁) ≪≫
        (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).mapIso
          (ModuleCat.ExtendScalars.objSelfIso σ)) ≪≫
      (HomologicalComplex.singleMapHomologicalComplex (ModuleCat.restrictScalars φ₂)
        (ComplexShape.up ℤ) 0).app (ModuleCat.of S₂ S₂)) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} R₂) 0).app
      ((ModuleCat.restrictScalars φ₂).obj (ModuleCat.of S₂ S₂))).symm

/-- **Finite Tor dimension localizes.** If `φ : R → A` has finite Tor dimension and `σ : A → B`,
`τ : R → C` are localizations with `σ ∘ φ = ψ ∘ τ`, then `ψ : C → B` has finite Tor dimension. -/
theorem hasFiniteTorDimensionRingHom_of_isLocalization {R A B C : Type u} [CommRing R]
    [CommRing A] [CommRing B] [CommRing C] (φ : R →+* A) (σ : A →+* B) (τ : R →+* C)
    (ψ : C →+* B) (hcomm : σ.comp φ = ψ.comp τ) (P : Submonoid A)
    (hσ : letI := σ.toAlgebra; IsLocalization P B) (Q : Submonoid R)
    (hτ : letI := τ.toAlgebra; IsLocalization Q C) (h : HasFiniteTorDimensionRingHom φ) :
    HasFiniteTorDimensionRingHom ψ := by
  obtain ⟨a, b, hab⟩ := h
  let M := (CochainComplex.singleFunctor (ModuleCat.{u} A) 0).obj (ModuleCat.of A A)
  have h₁ : HasTorAmplitudeCanonical R
      (DerivedCategory.Q.obj ((CochainComplex.restrictScalars φ).obj M)) a b :=
    BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso
      (DerivedCategory.Q.mapIso ((HomologicalComplex.singleMapHomologicalComplex
        (ModuleCat.restrictScalars φ) (ComplexShape.up ℤ) 0).app (ModuleCat.of A A)).symm)
      a b hab
  have h₂ := Stacks.Duality.hasTorAmplitudeCanonical_restrictScalars_extendScalars_of_isLocalization
    φ σ τ ψ hcomm P hσ Q hτ M a b h₁
  refine ⟨a, b, BaseChangeTorAmplitude.hasTorAmplitudeCanonical_of_iso ?_ a b h₂⟩
  exact DerivedCategory.Q.mapIso ((CochainComplex.restrictScalars ψ).mapIso
      ((HomologicalComplex.singleMapHomologicalComplex (ModuleCat.extendScalars σ)
          (ComplexShape.up ℤ) 0).app (ModuleCat.of A A) ≪≫
        (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).mapIso
          (ModuleCat.ExtendScalars.objSelfIso σ)) ≪≫
      (HomologicalComplex.singleMapHomologicalComplex (ModuleCat.restrictScalars ψ)
        (ComplexShape.up ℤ) 0).app (ModuleCat.of B B))

/-- **From finite Tor dimension on affine opens to the stalks.** If for all affine opens `V ⊆ S`
and `V' ⊆ g⁻¹(V)` the ring map `𝒪_S(V) ⟶ 𝒪_{S'}(V')` has finite Tor dimension, then so does every
stalk map `𝒪_{S, g(s')} ⟶ 𝒪_{S', s'}` of `g`: both local rings are localizations of the rings of
sections over affine neighbourhoods. -/
theorem hasFiniteTorDimensionRingHom_stalkMap_of_appLE {S S' : Scheme.{u}} (g : S' ⟶ S)
    (hg : ∀ (V : S.Opens) (V' : S'.Opens), IsAffineOpen V → IsAffineOpen V' →
      ∀ hle : V' ≤ g ⁻¹ᵁ V, HasFiniteTorDimensionRingHom (g.appLE V V' hle).hom)
    (s' : S') : HasFiniteTorDimensionRingHom (g.stalkMap s').hom := by
  obtain ⟨_, ⟨V, hV, rfl⟩, hgs, -⟩ := S.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (g s')) isOpen_univ
  obtain ⟨_, ⟨V', hV', rfl⟩, hs', hle⟩ := S'.isBasis_affineOpens.exists_subset_of_mem_open
    (show s' ∈ (g ⁻¹ᵁ V : S'.Opens) from hgs) (g ⁻¹ᵁ V).isOpen
  exact hasFiniteTorDimensionRingHom_of_isLocalization (g.appLE V V' hle).hom
    (S'.presheaf.germ V' s' hs').hom (S.presheaf.germ V (g s') hgs).hom (g.stalkMap s').hom
    (Stacks.Duality.germ_comp_appLE g hle s' hs') _ (hV'.isLocalization_stalk ⟨s', hs'⟩) _
    (hV.isLocalization_stalk ⟨g s', hgs⟩) (hg V V' hV hV' hle)

/-- **The base stalk map of a square lying over `g` through open immersions has finite Tor
dimension.** Let `Y → X₂ → S₂ ← S₂'` be a commutative square, `iS : S₂ ⟶ S` and `iS' : S₂' ⟶ S'`
open immersions with `g₂ ≫ iS = iS' ≫ g`, and `y` a point of `Y` at whose image `s'` in `S'` the
stalk map of `g` has finite Tor dimension. Then the base stalk map of the square at `y` makes
`𝒪_{S₂', f₂'(y)}` of Tor amplitude in some interval over `𝒪_{S₂, f₂(g₂'(y))}`. -/
theorem exists_hasTorAmplitudeCanonical_baseStalkMap {X₂ Y S₂ S₂' S S' : Scheme.{u}}
    (f₂ : X₂ ⟶ S₂) (g₂ : S₂' ⟶ S₂) (f₂' : Y ⟶ S₂') (g₂' : Y ⟶ X₂) (w₂ : g₂' ≫ f₂ = f₂' ≫ g₂)
    (g : S' ⟶ S) (iS : S₂ ⟶ S) (iS' : S₂' ⟶ S') [IsOpenImmersion iS] [IsOpenImmersion iS']
    (hgS : g₂ ≫ iS = iS' ≫ g) (y : Y)
    (hg : HasFiniteTorDimensionRingHom (g.stalkMap (iS' (f₂' y))).hom) :
    ∃ a b : ℤ, HasTorAmplitudeCanonical (S₂.presheaf.stalk (f₂ (g₂' y)))
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (S₂.presheaf.stalk (f₂ (g₂' y)))) 0).obj
        ((ModuleCat.restrictScalars (baseStalkMap f₂ g₂ f₂' g₂' w₂ y)).obj
          (ModuleCat.of (S₂'.presheaf.stalk (f₂' y)) (S₂'.presheaf.stalk (f₂' y))))) a b := by
  have hw : f₂ (g₂' y) = g₂ (f₂' y) := congrArg (fun k : Y ⟶ S₂ => k y) w₂
  have hgS' : iS (g₂ (f₂' y)) = g (iS' (f₂' y)) :=
    congrArg (fun k : S₂' ⟶ S => k (f₂' y)) hgS
  have hpt : g (iS' (f₂' y)) = iS (f₂ (g₂' y)) := by rw [hw, hgS']
  let τ := (S.presheaf.stalkCongr (.of_eq hpt)).hom ≫ iS.stalkMap (f₂ (g₂' y))
  let σ := iS'.stalkMap (f₂' y)
  have hτ : Function.Bijective τ.hom := ConcreteCategory.bijective_of_isIso τ
  have hσ : Function.Bijective σ.hom := ConcreteCategory.bijective_of_isIso σ
  refine exists_hasTorAmplitudeCanonical_of_bijective (g.stalkMap (iS' (f₂' y))).hom
    (baseStalkMap f₂ g₂ f₂' g₂' w₂ y) τ.hom hτ σ.hom hσ ?_ hg
  -- `σ ∘ g_{s'} = (g₂ ≫ iS)_{f₂' y}` and the base stalk map is `g₂` at `f₂' y` after a transport
  have e₁ := Scheme.Hom.stalkMap_comp iS' g (f₂' y)
  have e₂ := Scheme.Hom.stalkMap_comp g₂ iS (f₂' y)
  have e₄ := Scheme.Hom.stalkMap_congr_point iS (f₂ (g₂' y)) (g₂ (f₂' y)) hw
  have key : g.stalkMap (iS' (f₂' y)) ≫ σ =
      τ ≫ (S₂.presheaf.stalkCongr (.of_eq hw)).hom ≫ g₂.stalkMap (f₂' y) := by
    dsimp only [σ, τ]
    rw [← e₁, Scheme.Hom.stalkMap_congr_hom (iS' ≫ g) (g₂ ≫ iS) hgS.symm (f₂' y), e₂,
      Category.assoc, reassoc_of% e₄]
    simp only [← Category.assoc]
    refine congrArg (· ≫ _) ?_
    simp only [TopCat.Presheaf.stalkCongr_hom]
    exact (TopCat.Presheaf.stalkSpecializes_comp _ _ _).symm
  exact congrArg CommRingCat.Hom.hom key

end AlgebraicGeometry

end
