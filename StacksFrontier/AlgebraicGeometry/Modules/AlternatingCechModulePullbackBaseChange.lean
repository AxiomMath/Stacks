module

public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleRefinementPullback
public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleBaseChangeComp

/-!
# The Čech pullback map commutes with base change

Let `a : X' ⟶ X` be a morphism over `Spec A`, and let `X₀ ⟶ X` and `X'₀ ⟶ X'` be base changes
along `Spec A' ⟶ Spec A`, with the induced `a₀ : X'₀ ⟶ X₀`. Then the Čech pullback map along
`a₀` on the inverse-image covers, applied to the base change of a Čech cochain, is the base
change of the Čech pullback map along `a`, once the two pullbacks `a₀^* g₀^* F` and
`g'₀^* a^* F` of `F` to `X'₀` are identified.

## Main results

* `Stacks.Cech.pullbackSquareIso_pullbackSections`: pulling a section back around a commutative
  square, in either order, agrees through the identification of the two pullbacks; this is the
  identity, tuple by tuple, behind the compatibility of the Čech pullback map with base change.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

noncomputable section

namespace Stacks.Cech

/-- Pulling back along equal morphisms: the identification of the two pullbacks carries the
pullback of a section along the first to its pullback along the second. -/
theorem pullbackCongr_app_pullbackSections {Y Z : Scheme.{u}} {h₁ h₂ : Y ⟶ Z} (h : h₁ = h₂)
    (M : Z.Modules) {V : Z.Opens} {T : Y.Opens} (hT₁ : T ≤ h₁ ⁻¹ᵁ V) (hT₂ : T ≤ h₂ ⁻¹ᵁ V)
    (x : Γ(M, V)) :
    ((Scheme.Modules.pullbackCongr h).hom.app M).app T
        (CechCochains.restr ((Scheme.Modules.pullback h₁).obj M).presheaf hT₁
          (pullbackSections h₁ M V x)) =
      CechCochains.restr ((Scheme.Modules.pullback h₂).obj M).presheaf hT₂
        (pullbackSections h₂ M V x) := by
  subst h
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, NatTrans.id_app]
  rfl

variable {A A' : Type u} [CommRing A] [CommRing A']
  {X X' X₀ X'₀ : Scheme.{u}} (a : X' ⟶ X) (g₀ : X₀ ⟶ X) (g'₀ : X'₀ ⟶ X') (a₀ : X'₀ ⟶ X₀)
  (hcomm : a₀ ≫ g₀ = g'₀ ≫ a) (F : X.Modules)

/-- The identification `a₀^* g₀^* F ≅ g'₀^* a^* F` along a commutative square. -/
def pullbackSquareIso :
    (Scheme.Modules.pullback a₀).obj ((Scheme.Modules.pullback g₀).obj F) ≅
      (Scheme.Modules.pullback g'₀).obj ((Scheme.Modules.pullback a).obj F) :=
  (Scheme.Modules.pullbackComp a₀ g₀).app F ≪≫ (Scheme.Modules.pullbackCongr hcomm).app F ≪≫
    ((Scheme.Modules.pullbackComp g'₀ a).app F).symm

/-- On sections over `T`, the forward map of `pullbackSquareIso` is the composite of the forward
map of `pullbackComp a₀ g₀`, the forward map of `pullbackCongr hcomm` and the inverse map of
`pullbackComp g'₀ a`. -/
theorem pullbackSquareIso_hom_app_apply (T : X'₀.Opens)
    (y : Γ((Scheme.Modules.pullback a₀).obj ((Scheme.Modules.pullback g₀).obj F), T)) :
    ((pullbackSquareIso a g₀ g'₀ a₀ hcomm F).hom.app T) y =
      ((Scheme.Modules.pullbackComp g'₀ a).inv.app F).app T
        (((Scheme.Modules.pullbackCongr hcomm).hom.app F).app T
          (((Scheme.Modules.pullbackComp a₀ g₀).hom.app F).app T y)) :=
  rfl

/-- For an isomorphism `e : M ≅ N` of modules on a scheme, applying `e.hom` and then `e.inv` to
a section over `T` returns the section. -/
theorem iso_inv_app_hom_app {Y : Scheme.{u}} {M N : Y.Modules} (e : M ≅ N) (T : Y.Opens)
    (y : Γ(M, T)) : (e.inv.app T) ((e.hom.app T) y) = y := by
  rw [← ConcreteCategory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.hom_inv_id]
  rfl

/-- **Pulling a section back around a commutative square, in either order, agrees.** -/
theorem pullbackSquareIso_pullbackSections {V : X.Opens} {V₀ : X₀.Opens} {V' : X'.Opens}
    {T : X'₀.Opens} (hV₀ : V₀ ≤ g₀ ⁻¹ᵁ V) (hT₀ : T ≤ a₀ ⁻¹ᵁ V₀) (hV' : V' ≤ a ⁻¹ᵁ V)
    (hT' : T ≤ g'₀ ⁻¹ᵁ V') (x : Γ(F, V)) :
    ((pullbackSquareIso a g₀ g'₀ a₀ hcomm F).hom.app T)
        (CechCochains.restr _ hT₀ (pullbackSections a₀ _ V₀
          (CechCochains.restr _ hV₀ (pullbackSections g₀ F V x)))) =
      CechCochains.restr _ hT' (pullbackSections g'₀ _ V'
        (CechCochains.restr _ hV' (pullbackSections a F V x))) := by
  have hT₁ : T ≤ (a₀ ≫ g₀) ⁻¹ᵁ V := hT₀.trans (Scheme.Hom.preimage_mono a₀ hV₀)
  have hT₂ : T ≤ (g'₀ ≫ a) ⁻¹ᵁ V := hT'.trans (Scheme.Hom.preimage_mono g'₀ hV')
  rw [pullbackSquareIso_hom_app_apply, pullbackSections_comp g₀ a₀ F hV₀ hT₀ hT₁ x,
    pullbackCongr_app_pullbackSections hcomm F hT₁ hT₂ x,
    ← pullbackSections_comp a g'₀ F hV' hT' hT₂ x]
  exact iso_inv_app_hom_app ((Scheme.Modules.pullbackComp g'₀ a).app F) T _

variable {I I' : Type u} (U : I → X.Opens) (W : I' → X'.Opens) (π : I' → I)
  (hW : ∀ k, W k ≤ a ⁻¹ᵁ U (π k))

include hcomm hW in
/-- The inverse-image covers along the base change are again related by `π`. -/
theorem preimage_le_preimage_of_comm (k : I') :
    g'₀ ⁻¹ᵁ W k ≤ a₀ ⁻¹ᵁ (g₀ ⁻¹ᵁ U (π k)) := by
  intro x hx
  change (a₀ ≫ g₀) x ∈ U (π k)
  rw [hcomm]
  exact hW k hx

end Stacks.Cech

end

end
