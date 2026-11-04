module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyShiftedSingleCochains

/-!
# Compatible bilinear maps give compatible pairings of shifted sheaves

Let `X` be a topological space with a sheaf `𝒪_X` of commutative rings. A bilinear map
`β : ℱ × 𝒢 ⟶ ℋ` of sheaves of `𝒪_X`-modules gives the pairing
`Stacks.Cech.Hypercohomology.singlePairingAt a b (bilinearPairing β)` of the sheaves placed in
degrees `a`, `b` and `a + b`. If morphisms `u`, `v`, `w` carry `β₁` to `β₂`, in the sense that
`β₂(u x, v y) = w(β₁(x, y))` on sections, then the morphisms they induce on the shifted sheaves
carry the first pairing to the second, so that by `Stacks.Cech.Hypercohomology.cup_natural` they
are multiplicative on hypercohomology.

## Main results

* `Stacks.Cech.Hypercohomology.pairingHom_singlePairingAt`: the compatibility of the pairings.
* `Stacks.Cech.Hypercohomology.pairingHom_singlePairing`: the same for sheaves placed in degree
  zero.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.CechSheaf (SectionRing sectionsPresheafFunctor)
open Stacks.Cech.LinearCupProduct (tensorPresheafModules)
open scoped TensorProduct

universe u

namespace Stacks.Cech.Hypercohomology

attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize
attribute [local instance high] Stacks.Cech.Refinement.sectionCommRing

variable {X : TopCat.{u}} {O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

/-- The identification of the term of a shifted sheaf with the sections of the sheaf is natural,
in the direction from the shifted sheaf. -/
theorem singleXIsoAt_hom_naturality {F G : SheafOfModules.{u} (ringSheaf O)} (f : F ⟶ G) (a : ℤ) :
    ((Stacks.Cech.Refinement.sectionsComplex O).map (singlePlusMapAt O f a).hom).f a ≫
        (singleXIsoAt O G a a rfl).hom =
      (singleXIsoAt O F a a rfl).hom ≫ (sectionsPresheafFunctor ⊤).map f := by
  rw [← cancel_epi (singleXIsoAt O F a a rfl).inv, ← Category.assoc,
    singleXIsoAt_inv_naturality, Category.assoc, Iso.inv_hom_id, Category.comp_id,
    Iso.inv_hom_id_assoc]

/-- **Morphisms carrying one bilinear map to another carry the induced pairings of shifted
sheaves to one another.** -/
theorem pairingHom_singlePairingAt {F₁ G₁ H₁ F₂ G₂ H₂ : SheafOfModules.{u} (ringSheaf O)}
    (u : F₁ ⟶ F₂) (v : G₁ ⟶ G₂) (w : H₁ ⟶ H₂) (β₁ : Stacks.BilinearMap F₁.val G₁.val H₁.val)
    (β₂ : Stacks.BilinearMap F₂.val G₂.val H₂.val) (a b : ℤ)
    (h : ∀ (Z : (Opens X)ᵒᵖ) (x : F₁.val.obj Z) (y : G₁.val.obj Z),
      β₂.app Z (u.val.app Z x) (v.val.app Z y) = w.val.app Z (β₁.app Z x y)) :
    PairingHom O (singlePlusMapAt O u a) (singlePlusMapAt O v b) (singlePlusMapAt O w (a + b))
      (singlePairingAt a b (bilinearPairing β₁)) (singlePairingAt a b (bilinearPairing β₂)) := by
  intro p q n hn
  by_cases hpq : p = a ∧ q = b
  · obtain ⟨rfl, rfl⟩ := hpq
    subst hn
    have hβ : bilinearPairing β₁ ≫ (sectionsPresheafFunctor ⊤).map w =
        ((tensorPresheafModules.{u} (SectionRing (ringSheaf O) ⊤)).map
            ((sectionsPresheafFunctor ⊤).map u)).app _ ≫
          ((tensorPresheafModules.{u} (SectionRing (ringSheaf O) ⊤)).obj _).map
            ((sectionsPresheafFunctor ⊤).map v) ≫ bilinearPairing β₂ :=
      NatTrans.ext (funext fun Z => ModuleCat.hom_ext (TensorProduct.ext' fun x y =>
        (h (op (unop Z).left) x y).symm))
    have key :
        ((tensorPresheafModules.{u} (SectionRing (ringSheaf O) ⊤)).map
            (((Stacks.Cech.Refinement.sectionsComplex O).map (singlePlusMapAt O u p).hom).f p)).app
            _ ≫
          ((tensorPresheafModules.{u} (SectionRing (ringSheaf O) ⊤)).obj _).map
            (((Stacks.Cech.Refinement.sectionsComplex O).map (singlePlusMapAt O v q).hom).f q) ≫
          ((tensorPresheafModules.{u} _).map (singleXIsoAt O F₂ p p rfl).hom).app _ ≫
          ((tensorPresheafModules.{u} _).obj _).map (singleXIsoAt O G₂ q q rfl).hom =
        ((tensorPresheafModules.{u} _).map (singleXIsoAt O F₁ p p rfl).hom).app _ ≫
          ((tensorPresheafModules.{u} _).obj _).map (singleXIsoAt O G₁ q q rfl).hom ≫
          ((tensorPresheafModules.{u} (SectionRing (ringSheaf O) ⊤)).map
            ((sectionsPresheafFunctor ⊤).map u)).app _ ≫
          ((tensorPresheafModules.{u} (SectionRing (ringSheaf O) ⊤)).obj _).map
            ((sectionsPresheafFunctor ⊤).map v) := by
      simp only [NatTrans.naturality_assoc]
      simp only [← NatTrans.comp_app_assoc, ← Functor.map_comp, singleXIsoAt_hom_naturality]
    rw [singlePairingAt_μ, singlePairingAt_μ]
    simp only [Category.assoc]
    rw [singleXIsoAt_inv_naturality, reassoc_of% hβ, reassoc_of% key]
  · rw [singlePairingAt_μ_of_ne _ _ _ p q n hn hpq, singlePairingAt_μ_of_ne _ _ _ p q n hn hpq]
    simp only [Limits.comp_zero, Limits.zero_comp]

/-- **Morphisms carrying one bilinear map to another carry the induced pairings of sheaves placed
in degree zero to one another.** -/
theorem pairingHom_singlePairing {F₁ G₁ H₁ F₂ G₂ H₂ : SheafOfModules.{u} (ringSheaf O)}
    (u : F₁ ⟶ F₂) (v : G₁ ⟶ G₂) (w : H₁ ⟶ H₂) (β₁ : Stacks.BilinearMap F₁.val G₁.val H₁.val)
    (β₂ : Stacks.BilinearMap F₂.val G₂.val H₂.val)
    (h : ∀ (Z : (Opens X)ᵒᵖ) (x : F₁.val.obj Z) (y : G₁.val.obj Z),
      β₂.app Z (u.val.app Z x) (v.val.app Z y) = w.val.app Z (β₁.app Z x y)) :
    PairingHom O (singlePlusMap O u) (singlePlusMap O v) (singlePlusMap O w)
      (singlePairing (bilinearPairing β₁)) (singlePairing (bilinearPairing β₂)) :=
  pairingHom_singlePairingAt u v w β₁ β₂ 0 0 h

end Stacks.Cech.Hypercohomology
