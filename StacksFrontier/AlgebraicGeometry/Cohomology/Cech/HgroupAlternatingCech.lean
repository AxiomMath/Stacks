module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.OrderedCechHgroup
public import StacksFrontier.AlgebraicGeometry.Perfect.ProperFlatGlobalSections
public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleBaseChangeComp
public import StacksFrontier.Algebra.Homology.RestrictScalarsHomology

/-!
# Cohomology of a quasi-coherent module as alternating Čech cohomology over the base, naturally

Let `f : X ⟶ Spec A` be a scheme over an affine base and `U : I → X.Opens` a covering of `X`,
indexed by a linearly ordered type, all of whose finite intersections are affine. For a
quasi-coherent `𝒪_X`-module `G` the cohomology group `Hᵖ(X, G)` is the homology of the
`A`-linear alternating Čech complex `Stacks.Cech.alternatingCechModuleComplex f U G`
([Stacks, Tags 01XD, 01FM]), and the identification is natural in `G`.

It is the identification `Stacks.Algebraization.hgroupIsoOrderedCechHomology` with the ordered
Čech complex, followed by the comparison of the ordered and the alternating complexes
([Stacks, Tag 01FJ]) and by restriction of scalars along `A ⟶ Γ(X, 𝒪_X)`, which is the identity
on cochains.

## Main definitions

* `Stacks.Cech.hgroupIsoAlternatingCechModuleHomology`: the identification.

## Main results

* `Stacks.Cech.hgroupIsoAlternatingCechModuleHomology_naturality`: its naturality.

## References

* [Stacks Project, Tag 01XD](https://stacks.math.columbia.edu/tag/01XD)
* [Stacks Project, Tag 01FJ](https://stacks.math.columbia.edu/tag/01FJ)
* [Stacks Project, Tag 01FM](https://stacks.math.columbia.edu/tag/01FM)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite
open Stacks.Cohomology.CechSheaf Stacks.AlgebraicGeometry.ProperFlatGlobalSections

universe u

namespace Stacks.Cech

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) {I : Type u}
  [LinearOrder I] (U : I → X.Opens) (hU : (⊤ : X.Opens) = ⨆ i, U i)
  (haff : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ k, U (s k)))

/-- Restriction of scalars along `A ⟶ Γ(X, 𝒪_X)` carries the `Γ(X, 𝒪_X)`-linear functoriality of
the alternating Čech complex to the `A`-linear one. -/
theorem alternatingCechModuleComplexIso_naturality {G G' : X.Modules} (ψ : G ⟶ G') :
    ((ModuleCat.restrictScalars.{u} (globalRingHom f).hom).mapHomologicalComplex
        (ComplexShape.up ℕ)).map (alternatingModuleMap ⊤ U hU ψ) ≫
      (alternatingCechModuleComplexIso f U hU G').hom =
    (alternatingCechModuleComplexIso f U hU G).hom ≫ alternatingCechModuleComplexMap f U ψ := by
  ext p s
  rfl

/-- **`Hᵖ(X, G)` is the homology of the alternating Čech complex of `A`-modules of an affine
covering with affine finite intersections**, as abelian groups, for a quasi-coherent `G`. -/
def hgroupIsoAlternatingCechModuleHomology (G : X.Modules) [G.IsQuasicoherent] (p : ℕ) :
    Hgroup X.ringCatSheaf ⊤ p G ≅
      (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).obj
        ((alternatingCechModuleComplex f U G).homology p) :=
  Stacks.Algebraization.hgroupIsoOrderedCechHomology X U hU haff G p ≪≫
    (forget₂ (ModuleCat.{u} (SectionRing X.ringCatSheaf ⊤)) AddCommGrpCat.{u}).mapIso
      (HomologicalComplex.homologyMapIso (orderedIsoAlternatingModuleComplex ⊤ U hU G) p) ≪≫
    (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).mapIso
      ((Stacks.Homology.RestrictScalars.restrictScalarsHomologyIso (globalRingHom f).hom
          (alternatingModuleComplex ⊤ U hU G) p).symm ≪≫
        HomologicalComplex.homologyMapIso (alternatingCechModuleComplexIso f U hU G) p)

/-- The identification, as a composite of three maps. -/
theorem hgroupIsoAlternatingCechModuleHomology_hom (G : X.Modules) [G.IsQuasicoherent] (p : ℕ) :
    (hgroupIsoAlternatingCechModuleHomology f U hU haff G p).hom =
      (Stacks.Algebraization.hgroupIsoOrderedCechHomology X U hU haff G p).hom ≫
        (forget₂ (ModuleCat.{u} (SectionRing X.ringCatSheaf ⊤)) AddCommGrpCat.{u}).map
          (HomologicalComplex.homologyMap (orderedIsoAlternatingModuleComplex ⊤ U hU G).hom p) ≫
        (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).map
          ((Stacks.Homology.RestrictScalars.restrictScalarsHomologyIso (globalRingHom f).hom
              (alternatingModuleComplex ⊤ U hU G) p).inv ≫
            HomologicalComplex.homologyMap (alternatingCechModuleComplexIso f U hU G).hom p) :=
  rfl

private theorem paste_three_squares {C : Type*} [Category* C] {a b c d a' b' c' d' : C}
    (f₀ : a ⟶ a') (x : a' ⟶ b') (y : b' ⟶ c') (z : c' ⟶ d') (x₀ : a ⟶ b) (y₀ : b ⟶ c)
    (z₀ : c ⟶ d) (g₁ : b ⟶ b') (g₂ : c ⟶ c') (g₃ : d ⟶ d') (h₁ : f₀ ≫ x = x₀ ≫ g₁)
    (h₂ : g₁ ≫ y = y₀ ≫ g₂) (h₃ : g₂ ≫ z = z₀ ≫ g₃) :
    f₀ ≫ x ≫ y ≫ z = x₀ ≫ y₀ ≫ z₀ ≫ g₃ := by
  rw [reassoc_of% h₁, reassoc_of% h₂, h₃]

private theorem inv_square {C : Type*} [Category* C] {a b c d : C} (x : a ⟶ b) (e : a ≅ c)
    (e' : b ≅ d) (y : c ⟶ d) (h : x ≫ e'.hom = e.hom ≫ y) : y ≫ e'.inv = e.inv ≫ x := by
  rw [Iso.eq_inv_comp, ← reassoc_of% h, Iso.hom_inv_id, Category.comp_id]

private theorem two_squares {C : Type*} [Category* C] {a b c d e f : C} (x : a ⟶ b)
    (y : b ⟶ d) (x' : a ⟶ c) (y' : c ⟶ d) (z : d ⟶ f) (z' : c ⟶ e) (w : e ⟶ f)
    (h₁ : x ≫ y = x' ≫ y') (h₂ : y' ≫ z = z' ≫ w) : x ≫ y ≫ z = x' ≫ z' ≫ w := by
  rw [reassoc_of% h₁, h₂]

/-- Homology maps carry a commuting square of chain maps to a commuting square. -/
private theorem homologyMap_square {C : Type*} [Category* C] [Preadditive C]
    [CategoryWithHomology C]
    {c : ComplexShape ℕ} (p : ℕ) {K L M N : HomologicalComplex C c} (a : K ⟶ L) (b : L ⟶ N)
    (a' : K ⟶ M) (b' : M ⟶ N) (h : a ≫ b = a' ≫ b') :
    HomologicalComplex.homologyMap a p ≫ HomologicalComplex.homologyMap b p =
      HomologicalComplex.homologyMap a' p ≫ HomologicalComplex.homologyMap b' p := by
  rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp, h]

/-- **The identification is natural in the quasi-coherent module.** -/
theorem hgroupIsoAlternatingCechModuleHomology_naturality {G G' : X.Modules} [G.IsQuasicoherent]
    [G'.IsQuasicoherent] (ψ : G ⟶ G') (p : ℕ) :
    (Hfunctor X.ringCatSheaf ⊤ p).map ψ ≫
        (hgroupIsoAlternatingCechModuleHomology f U hU haff G' p).hom =
      (hgroupIsoAlternatingCechModuleHomology f U hU haff G p).hom ≫
        (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).map
          (HomologicalComplex.homologyMap (alternatingCechModuleComplexMap f U ψ) p) := by
  have h₁ := Stacks.Algebraization.hgroupIsoOrderedCechHomology_naturality X U hU haff ψ p
  have h₂ := homologyMap_square p _ _ _ _ (orderedIsoAlternatingModuleComplex_naturality ⊤ U hU ψ)
  have h₃ := Stacks.Homology.RestrictScalars.restrictScalarsHomologyIso_naturality
    (globalRingHom f).hom (alternatingModuleMap ⊤ U hU ψ) p
  have h₄ := homologyMap_square p _ _ _ _ (alternatingCechModuleComplexIso_naturality f U hU ψ)
  have h₅ : (ModuleCat.restrictScalars.{u} (globalRingHom f).hom).map
        (HomologicalComplex.homologyMap (alternatingModuleMap ⊤ U hU ψ) p) ≫
        (Stacks.Homology.RestrictScalars.restrictScalarsHomologyIso (globalRingHom f).hom
          (alternatingModuleComplex ⊤ U hU G') p).inv ≫
        HomologicalComplex.homologyMap (alternatingCechModuleComplexIso f U hU G').hom p =
      (Stacks.Homology.RestrictScalars.restrictScalarsHomologyIso (globalRingHom f).hom
          (alternatingModuleComplex ⊤ U hU G) p).inv ≫
        HomologicalComplex.homologyMap (alternatingCechModuleComplexIso f U hU G).hom p ≫
        HomologicalComplex.homologyMap (alternatingCechModuleComplexMap f U ψ) p :=
    two_squares _ _ _ _ _ _ _ (inv_square _ _ _ _ h₃) h₄
  have h₆ : (forget₂ (ModuleCat.{u} (SectionRing X.ringCatSheaf ⊤)) AddCommGrpCat.{u}).map
        (HomologicalComplex.homologyMap (alternatingModuleMap ⊤ U hU ψ) p) ≫
        (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).map
          ((Stacks.Homology.RestrictScalars.restrictScalarsHomologyIso (globalRingHom f).hom
              (alternatingModuleComplex ⊤ U hU G') p).inv ≫
            HomologicalComplex.homologyMap (alternatingCechModuleComplexIso f U hU G').hom p) =
      (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).map
          ((Stacks.Homology.RestrictScalars.restrictScalarsHomologyIso (globalRingHom f).hom
              (alternatingModuleComplex ⊤ U hU G) p).inv ≫
            HomologicalComplex.homologyMap (alternatingCechModuleComplexIso f U hU G).hom p) ≫
        (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).map
          (HomologicalComplex.homologyMap (alternatingCechModuleComplexMap f U ψ) p) := by
    have := congrArg (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).map h₅
    simp only [Functor.map_comp] at this ⊢
    exact this
  have h₂' := congrArg (forget₂ (ModuleCat.{u} (SectionRing X.ringCatSheaf ⊤))
    AddCommGrpCat.{u}).map h₂
  simp only [Functor.map_comp] at h₂'
  rw [hgroupIsoAlternatingCechModuleHomology_hom, hgroupIsoAlternatingCechModuleHomology_hom]
  exact paste_three_squares _ _ _ _ _ _ _ _ _ _ h₁ h₂' h₆

end Stacks.Cech

end
