module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.KummerDirectImageCoboundary
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.ConnectingMapDeltaFunctor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedGeometricStalkSections

/-!
# The Kummer coboundary commutes with base change

Let `h ≫ f' = e ≫ g` be a commutative square of schemes, with `g : T ⟶ S` and `h : Y ⟶ X'`, and
let `N` be invertible on `T` and on `Y`. The inverse image along `e` of the Kummer sequence of `T`
maps to the Kummer sequence of `Y` (`Stacks.EtaleCohomology.Purity.kummerSequencePullbackMap`).
The base change maps of [Stacks, Tag 0F02] then carry the Kummer coboundary
`∂_g : g_* 𝐆_m ⟶ R¹ g_* μ_N` to `∂_h`: in degree one the base change map follows `f'⁻¹ ∂_g`, in
degree zero the underived base change map `f'⁻¹ g_* ⟶ h_* e⁻¹` precedes `∂_h`
(`Stacks.EtaleCohomology.Purity.kummerDirectImageδ_baseChange`).

This is the compatibility of the connecting morphisms of the higher direct images with base
change (`Stacks.EtaleCohomology.higherBaseChangeMapAb_comp_δ`), read through the identification
of the degree-zero base change map with the underived one
(`Stacks.EtaleCohomology.map_rightDerivedZeroUnit_comp_higherBaseChangeMapAb_zero`), in the
normalisation of `∂` by `Stacks.RightDerivedPlus.rightDerivedZeroUnit`
(`Stacks.EtaleCohomology.Purity.kummerDirectImageδ_eq`). It is stated in the standard model of
the derived categories, in which the base change maps are defined.

## Main definitions

* `Stacks.EtaleCohomology.Purity.kummerSequencePullbackMap`.

## Main results

* `Stacks.EtaleCohomology.Purity.kummerDirectImageδ_baseChange`.

## Implementation notes

The statements are spelled with the terms `(kummerSequence _ N).X₁`, `(kummerSequence _ N).X₃` and
the degree `0 + 1`, as the `δ`-functor produces them, rather than with `μ_N`, `𝐆_m` and `1`: the
two spellings are definitionally equal, but the kernel's check of the conversion of the whole
identity exceeds its default budget.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology.Purity

open Stacks.Kummer

attribute [local instance] HasDerivedCategory.standard

/-- **The inverse image of the Kummer sequence maps to the Kummer sequence**: the comparison
`e⁻¹ 𝐆_m ⟶ 𝐆_m` on the last two terms and `e⁻¹ μ_N ⟶ μ_N` on the first, read through the
identification of the two inverse images of abelian étale sheaves. -/
def kummerSequencePullbackMap {Y T : Scheme.{u}} (e : Y ⟶ T) (N : ℕ) :
    (kummerSequence.{u, 0} T N).map (smallEtalePullbackAb e) ⟶ kummerSequence.{u, 0} Y N :=
  ((kummerSequence.{u, 0} T N).mapNatIso (smallEtalePullbackAbIsoEtaleAbelianInverseImage e)).hom ≫
    kummerSequenceInverseImageMap.{u, 0} e N

/-- The degree-zero identification `F ⟶ R⁰F` used to normalise `∂` is natural. -/
theorem rightDerivedZeroUnit_comp_rightDerivedIso_inv_naturality {C D : Type*} [Category C]
    [Category D] [Abelian C] [Abelian D] [HasDerivedCategory C] [HasDerivedCategory D]
    [EnoughInjectives C] (F : C ⥤ D) [F.Additive] {X Y : C} (φ : X ⟶ Y) :
    F.map φ ≫ (Stacks.RightDerivedPlus.rightDerivedZeroUnit F Y ≫
        (Stacks.DerivedIndexing.rightDerivedIso F 0).inv.app Y) =
      (Stacks.RightDerivedPlus.rightDerivedZeroUnit F X ≫
        (Stacks.DerivedIndexing.rightDerivedIso F 0).inv.app X) ≫ (F.rightDerived 0).map φ := by
  rw [reassoc_of% (Stacks.DerivedFunctor.rightDerivedZeroUnit_naturality F φ), Category.assoc]
  exact congrArg (_ ≫ ·) ((Stacks.DerivedIndexing.rightDerivedIso F 0).inv.naturality φ)

/-- The algebra of `Stacks.EtaleCohomology.Purity.kummerDirectImageδ_baseChange`, on variables
(stated so that its hypotheses are consumed up to definitional unfolding of their objects). -/
theorem baseChange_chain {𝒳 : Type*} [Category* 𝒳] {o₀ o₁ o₂ o₃ o₄ o₅ p₁ p₂ p₃ : 𝒳}
    {Fab : o₀ ⟶ o₂} {Fa : o₀ ⟶ o₁} {Fb : o₁ ⟶ o₂} {B₁ : o₂ ⟶ o₃} {R₁ : o₃ ⟶ o₄}
    {B₀ : o₁ ⟶ p₁} {R₀ : p₁ ⟶ p₂} {δ : p₂ ⟶ o₄} {s : o₀ ⟶ o₅} {η' : o₅ ⟶ p₁}
    {σ : o₅ ⟶ p₃} {η : p₃ ⟶ p₂}
    (hab : Fab = Fa ≫ Fb) (hc : B₀ ≫ R₀ ≫ δ = Fb ≫ B₁ ≫ R₁) (hz : Fa ≫ B₀ = s ≫ η')
    (hn : σ ≫ η = η' ≫ R₀) : Fab ≫ B₁ ≫ R₁ = s ≫ σ ≫ η ≫ δ := by
  rw [hab, Category.assoc, ← hc, reassoc_of% hz, reassoc_of% hn]

variable {X' Y S T : Scheme.{u}} (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T)
  (w : h ≫ f' = e ≫ g) {N : ℕ} (hN0 : N ≠ 0) (hNT : IsUnit ((N : ℕ) : Γ(T, ⊤)))
  (hNY : IsUnit ((N : ℕ) : Γ(Y, ⊤)))

/-- `Stacks.EtaleCohomology.higherBaseChangeMapAb_comp_δ` in degree zero, elaborated in this
file (the kernel checks its instantiation at the Kummer sequences against this local form far
faster than against the original). -/
private theorem higherBaseChangeMapAb_comp_δ_zero
    {S₀ : ShortComplex (Sheaf (smallEtaleTopology T) Ab.{u + 1})} (hS : S₀.ShortExact)
    {S' : ShortComplex (Sheaf (smallEtaleTopology Y) Ab.{u + 1})} (hS' : S'.ShortExact)
    (σ : S₀.map (smallEtalePullbackAb e) ⟶ S') :
    (higherBaseChangeMapAb f' g h e w 0).app S₀.X₃ ≫
        ((smallEtalePushforwardAb h).rightDerived 0).map σ.τ₃ ≫
        (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
          (smallEtalePushforwardAb h)).δ hS' 0 =
      (smallEtalePullbackAb f').map
          ((Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
            (smallEtalePushforwardAb g)).δ hS 0) ≫
        (higherBaseChangeMapAb f' g h e w (0 + 1)).app S₀.X₁ ≫
        ((smallEtalePushforwardAb h).rightDerived (0 + 1)).map σ.τ₁ :=
  higherBaseChangeMapAb_comp_δ f' g h e w 0 hS hS' σ

/-- `Stacks.EtaleCohomology.higherBaseChangeMapAb_comp_δ` at the Kummer sequences, in degree
zero, for any morphism `σ` from the inverse image of the Kummer sequence of `T` to the Kummer
sequence of `Y`. -/
theorem higherBaseChangeMapAb_comp_δ_kummerSequence
    (σ : (kummerSequence.{u, 0} T N).map (smallEtalePullbackAb e) ⟶ kummerSequence.{u, 0} Y N) :
    (higherBaseChangeMapAb f' g h e w 0).app (kummerSequence.{u, 0} T N).X₃ ≫
        ((smallEtalePushforwardAb h).rightDerived 0).map σ.τ₃ ≫
          (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
            (smallEtalePushforwardAb h)).δ (kummerSequence_shortExact.{u, 0} Y hN0 hNY) 0 =
      (smallEtalePullbackAb f').map
          ((Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
            (smallEtalePushforwardAb g)).δ (kummerSequence_shortExact.{u, 0} T hN0 hNT) 0) ≫
        (higherBaseChangeMapAb f' g h e w (0 + 1)).app (kummerSequence.{u, 0} T N).X₁ ≫
          ((smallEtalePushforwardAb h).rightDerived (0 + 1)).map σ.τ₁ :=
  higherBaseChangeMapAb_comp_δ_zero f' g h e w
    (kummerSequence_shortExact.{u, 0} T hN0 hNT) (kummerSequence_shortExact.{u, 0} Y hN0 hNY) σ

private theorem kummerDirectImageδ_baseChange_aux
    (σ : (kummerSequence.{u, 0} T N).map (smallEtalePullbackAb e) ⟶ kummerSequence.{u, 0} Y N) :
    (smallEtalePullbackAb f').map
        ((Stacks.RightDerivedPlus.rightDerivedZeroUnit (smallEtalePushforwardAb g)
            (kummerSequence.{u, 0} T N).X₃ ≫
          (Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb g) 0).inv.app
            (kummerSequence.{u, 0} T N).X₃) ≫
          (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
            (smallEtalePushforwardAb g)).δ (kummerSequence_shortExact.{u, 0} T hN0 hNT) 0) ≫
        (higherBaseChangeMapAb f' g h e w (0 + 1)).app (kummerSequence.{u, 0} T N).X₁ ≫
          ((smallEtalePushforwardAb h).rightDerived (0 + 1)).map σ.τ₁ =
      (smallEtaleBaseChangeAb f' g h e w).app (kummerSequence.{u, 0} T N).X₃ ≫
        (smallEtalePushforwardAb h).map σ.τ₃ ≫
          (Stacks.RightDerivedPlus.rightDerivedZeroUnit (smallEtalePushforwardAb h)
              (kummerSequence.{u, 0} Y N).X₃ ≫
            (Stacks.DerivedIndexing.rightDerivedIso (smallEtalePushforwardAb h) 0).inv.app
              (kummerSequence.{u, 0} Y N).X₃) ≫
          (Stacks.DerivedIndexing.rightDerivedDeltaFunctorOfEnoughInjectives
            (smallEtalePushforwardAb h)).δ (kummerSequence_shortExact.{u, 0} Y hN0 hNY) 0 :=
  baseChange_chain ((smallEtalePullbackAb f').map_comp _ _)
    (higherBaseChangeMapAb_comp_δ_kummerSequence f' g h e w hN0 hNT hNY σ)
    (map_rightDerivedZeroUnit_comp_higherBaseChangeMapAb_zero f' g h e w
      (kummerSequence.{u, 0} T N).X₃)
    (rightDerivedZeroUnit_comp_rightDerivedIso_inv_naturality (smallEtalePushforwardAb h) σ.τ₃)

/-- **The Kummer coboundary commutes with base change.** For a commutative square
`h ≫ f' = e ≫ g` and a morphism `σ` from the inverse image of the Kummer sequence of `T` to the
Kummer sequence of `Y` (e.g. `Stacks.EtaleCohomology.Purity.kummerSequencePullbackMap`), the
inverse image of `∂_g : g_* 𝐆_m ⟶ R¹ g_* μ_N` followed by the degree-one base change map and
`σ` on `μ_N` is the underived base change map followed by `σ` on `𝐆_m` and `∂_h`. -/
theorem kummerDirectImageδ_baseChange
    (σ : (kummerSequence.{u, 0} T N).map (smallEtalePullbackAb e) ⟶ kummerSequence.{u, 0} Y N) :
    (smallEtalePullbackAb f').map (kummerDirectImageδ g hN0 hNT) ≫
        (higherBaseChangeMapAb f' g h e w (0 + 1)).app (kummerSequence.{u, 0} T N).X₁ ≫
          ((smallEtalePushforwardAb h).rightDerived (0 + 1)).map σ.τ₁ =
      (smallEtaleBaseChangeAb f' g h e w).app (kummerSequence.{u, 0} T N).X₃ ≫
        (smallEtalePushforwardAb h).map σ.τ₃ ≫ kummerDirectImageδ h hN0 hNY := by
  rw [kummerDirectImageδ_eq, kummerDirectImageδ_eq]
  exact kummerDirectImageδ_baseChange_aux f' g h e w hN0 hNT hNY σ

end Stacks.EtaleCohomology.Purity

end
