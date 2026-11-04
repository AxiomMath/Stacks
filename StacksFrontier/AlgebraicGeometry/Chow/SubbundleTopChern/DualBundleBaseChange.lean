module

public import StacksFrontier.AlgebraicGeometry.Chow.SubbundleTopChern.ZeroSectionFormula
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.DualSectionsInfinitesimal
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleBaseChange
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Base change of the vector bundle of a dual

For `g : T ⟶ X` and a finite locally free `𝒪_X`-module `ℰ`, the dual commutes with pullback,
`g^*(ℰ^∨) ≅ (g^*ℰ)^∨` (Tag 0GMX at `𝒢 = 𝒪`), and the vector bundle commutes with base change, so
`𝐕((g^*ℰ)^∨) = 𝐕(ℰ^∨) ×_X T`. The zero section of `𝐕((g^*ℰ)^∨)` is the base change of the zero
section of `𝐕(ℰ^∨)`: the square formed by the two zero sections, `g` and `𝐕((g^*ℰ)^∨) ⟶ 𝐕(ℰ^∨)` is
cartesian.

## Main definitions

* `Stacks.Chow.dualBundleBaseChangeMap` — the morphism `𝐕((g^*ℰ)^∨) ⟶ 𝐕(ℰ^∨)`.

## Main results

* `Stacks.Chow.isPullback_dualBundleBaseChangeMap` — the base-change square.
* `Stacks.Chow.isPullback_dualVectorBundleZeroSection_dualBundleBaseChangeMap` — the zero sections.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits AlgebraicGeometry.Scheme.Modules
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.Chow

/-- The pullback `g^*ℰ` of a finite locally free `𝒪_X`-module `ℰ` along `g : T ⟶ X` is finite
locally free. -/
instance isFiniteLocallyFree_pullback_obj' {T X : Scheme.{u}} (g : T ⟶ X) (E : X.Modules)
    [h : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E] :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      ((Scheme.Modules.pullback g).obj E) :=
  isFiniteLocallyFree_pullback g E h

variable {T X : Scheme.{u}} (g : T ⟶ X) (E : X.Modules)
  [hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]

/-- **The morphism `𝐕((g^*ℰ)^∨) ⟶ 𝐕(ℰ^∨)`** over `g`: the identification
`(g^*ℰ)^∨ ≅ g^*(ℰ^∨)` followed by the base-change morphism of `𝐕(ℰ^∨)`. -/
def dualBundleBaseChangeMap :
    dualVectorBundle ((Scheme.Modules.pullback g).obj E) ⟶ dualVectorBundle E :=
  (vectorBundleMap T (Stacks.FundamentalGroup.pullbackDualSheafIso g E hE).hom).left ≫
    vectorBundleBaseChangeMap g (dualSheaf E)

/-- The identification `𝐕((g^*ℰ)^∨) ≅ 𝐕(g^*(ℰ^∨))` induced by `g^*(ℰ^∨) ≅ (g^*ℰ)^∨`. -/
def dualBundlePullbackIso :
    dualVectorBundle ((Scheme.Modules.pullback g).obj E) ≅
      vectorBundle T ((Scheme.Modules.pullback g).obj (dualSheaf E)) where
  hom := (vectorBundleMap T (Stacks.FundamentalGroup.pullbackDualSheafIso g E hE).hom).left
  inv := (vectorBundleMap T (Stacks.FundamentalGroup.pullbackDualSheafIso g E hE).inv).left
  hom_inv_id := congrArg (fun h => h.left)
    ((vectorBundleMap_comp T (Stacks.FundamentalGroup.pullbackDualSheafIso g E hE).inv
      (Stacks.FundamentalGroup.pullbackDualSheafIso g E hE).hom).symm.trans
      ((congrArg (vectorBundleMap T) (Iso.inv_hom_id _)).trans (vectorBundleMap_id T)))
  inv_hom_id := congrArg (fun h => h.left)
    ((vectorBundleMap_comp T (Stacks.FundamentalGroup.pullbackDualSheafIso g E hE).hom
      (Stacks.FundamentalGroup.pullbackDualSheafIso g E hE).inv).symm.trans
      ((congrArg (vectorBundleMap T) (Iso.hom_inv_id _)).trans (vectorBundleMap_id T)))

/-- `dualBundleBaseChangeMap g E` is `dualBundlePullbackIso g E` followed by the base-change
morphism of `𝐕(ℰ^∨)`. -/
theorem dualBundleBaseChangeMap_eq :
    dualBundleBaseChangeMap g E =
      (dualBundlePullbackIso g E).hom ≫ vectorBundleBaseChangeMap g (dualSheaf E) := rfl

/-- **The vector bundle of the dual of a pullback is the base change of the vector bundle of the
dual**: `𝐕((g^*ℰ)^∨) = 𝐕(ℰ^∨) ×_X T`. -/
@[ega "IV 18.5.1" "partial"]
theorem isPullback_dualBundleBaseChangeMap :
    IsPullback (dualBundleBaseChangeMap g E)
      (dualVectorBundleToBase ((Scheme.Modules.pullback g).obj E)) (dualVectorBundleToBase E)
      g := by
  have hA : IsPullback (dualBundlePullbackIso g E).hom
      (dualVectorBundleToBase ((Scheme.Modules.pullback g).obj E))
      (vectorBundleToBase T ((Scheme.Modules.pullback g).obj (dualSheaf E))) (𝟙 T) :=
    IsPullback.of_horiz_isIso ⟨(vectorBundleMap_left_comp T
      (Stacks.FundamentalGroup.pullbackDualSheafIso g E hE).hom).trans
        (Category.comp_id _).symm⟩
  have h := hA.paste_horiz (isPullback_vectorBundleBaseChangeMap g (dualSheaf E))
  rw [Category.id_comp] at h
  exact h

/-- **The base-change morphism carries the zero section to the zero section.** -/
theorem dualVectorBundleZeroSection_comp_dualBundleBaseChangeMap :
    dualVectorBundleZeroSection ((Scheme.Modules.pullback g).obj E) ≫
        dualBundleBaseChangeMap g E =
      g ≫ dualVectorBundleZeroSection E := by
  refine (Category.assoc _ _ _).symm.trans ?_
  refine Eq.trans ?_ (vectorBundleOverZeroSection_comp_vectorBundleBaseChangeMap g (dualSheaf E))
  exact congrArg (· ≫ vectorBundleBaseChangeMap g (dualSheaf E)) (congrArg (fun h => h.left)
    (vectorBundleOverZeroSection_comp_vectorBundleMap
      (Stacks.FundamentalGroup.pullbackDualSheafIso g E hE).hom))

/-- **The zero section of `𝐕((g^*ℰ)^∨)` is the base change of the zero section of `𝐕(ℰ^∨)`.** -/
theorem isPullback_dualVectorBundleZeroSection_dualBundleBaseChangeMap :
    IsPullback g (dualVectorBundleZeroSection ((Scheme.Modules.pullback g).obj E))
      (dualVectorBundleZeroSection E) (dualBundleBaseChangeMap g E) := by
  refine IsPullback.of_bot ?_
    (dualVectorBundleZeroSection_comp_dualBundleBaseChangeMap g E).symm
    (isPullback_dualBundleBaseChangeMap g E)
  rw [dualVectorBundleZeroSection_comp, dualVectorBundleZeroSection_comp]
  exact IsPullback.of_vert_isIso ⟨by simp⟩

end Stacks.Chow

end
