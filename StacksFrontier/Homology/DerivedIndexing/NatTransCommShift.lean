module

public import StacksFrontier.Algebra.Homology.HomotopyCategory.InducedCommShift
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# The morphism of right derived functors induced by a natural transformation commutes with the
shift

Let `τ : F₁ ⟶ F₂` be a natural transformation of additive functors `𝒜 ⥤ ℬ`, `𝒜` with enough
injectives. The induced morphism `RF₁ ⟶ RF₂` of right derived functors on bounded below derived
categories, `Stacks.DerivedIndexing.rightDerivedFunctorPlusNatTrans`, is produced by the
universal property of right derivation; it commutes with the shift by `ℤ`.

## Main results

* `Stacks.DerivedIndexing.natTransCommShift_rightDerivedFunctorPlusNatTrans`: the induced
  morphism of right derived functors commutes with the shift.
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits DerivedCategory

namespace Stacks.DerivedIndexing

attribute [local instance 2000]
  HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

attribute [local instance] commShiftRightDerivedFunctorPlus
  natTransCommShiftRightDerivedFunctorPlusUnit

variable {C D : Type*} [Category* C] [Category* D] [Abelian C] [Abelian D]
  [HasDerivedCategory C] [HasDerivedCategory D] [EnoughInjectives C]
  {F₁ F₂ : C ⥤ D} [F₁.Additive] [F₂.Additive] (τ : F₁ ⟶ F₂)

/-- **The morphism `RF₁ ⟶ RF₂` induced by `τ : F₁ ⟶ F₂` commutes with the shift by `ℤ`.** For
each `a` the equation is between transformations out of `shiftFunctor D⁺(𝒜) a ⋙ RF₁`, itself a
right derived functor, so it is checked after composing with its unit, where it reduces to the
shift-compatibility of the units of `RF₁` and `RF₂` and of `τ` applied degreewise. -/
lemma natTransCommShift_rightDerivedFunctorPlusNatTrans :
    NatTrans.CommShift (rightDerivedFunctorPlusNatTrans τ) ℤ := by
  refine ⟨fun a => ?_⟩
  refine Functor.rightDerived_ext _
    (Functor.IsRightDerivedFunctor.precomposeShiftNatTrans
      F₁.rightDerivedFunctorPlus F₁.rightDerivedFunctorPlusUnith a)
    (HomotopyCategory.Plus.quasiIso C) _ _ _ (NatTrans.ext (funext fun K => ?_))
  have key (G : C ⥤ D) [G.Additive] :
      G.rightDerivedFunctorPlusUnith.app ((shiftFunctor (HomotopyCategory.Plus C) a).obj K) ≫
          G.rightDerivedFunctorPlus.map
            ((Functor.commShiftIso DerivedCategory.Plus.Qh a).hom.app K) ≫
          (Functor.commShiftIso G.rightDerivedFunctorPlus a).hom.app
            (DerivedCategory.Plus.Qh.obj K) =
        (Functor.commShiftIso (G.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) a).hom.app K ≫
          (shiftFunctor (DerivedCategory.Plus D) a).map (G.rightDerivedFunctorPlusUnith.app K) :=
    Functor.IsRightDerivedFunctor.comp_map_commShiftIso_hom_app _ _
      (HomotopyCategory.Plus.quasiIso C) ℤ a K
  have hnat := (rightDerivedFunctorPlusNatTrans τ).naturality
    ((Functor.commShiftIso DerivedCategory.Plus.Qh a).hom.app K)
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Category.assoc, Functor.IsRightDerivedFunctor.precomposeShiftNatTrans_app]
  rw [reassoc_of% (key F₁), ← Functor.map_comp, rightDerivedFunctorPlusNatTrans_app,
    reassoc_of% hnat, reassoc_of% (rightDerivedFunctorPlusNatTrans_app τ _), key F₂,
    Functor.map_comp, ← assoc, ← assoc]
  exact NatTrans.shift_app_comm
    (Functor.whiskerRight (Functor.mapHomotopyCategoryPlusNatTrans τ) DerivedCategory.Plus.Qh)
    a K =≫ _

end Stacks.DerivedIndexing
