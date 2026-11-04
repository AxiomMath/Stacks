module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ExtensionByZeroIntegralTwist

/-!
# Extension by zero of a twist, compared through the restriction

Let `Λ` be a ring, `j : V ⟶ V̄` an étale monomorphism and `σ : V̄ ⟶ V̄` an integral morphism with
a cartesian square `σ_V ≫ j = j ≫ σ`. A map `l : j^{-1} G ⟶ G'` intertwining the restriction of
`ε : G ⟶ σ_* G` with a twist `ε' : G' ⟶ σ_{V,*} G'` gives, after extension by zero, a map
intertwining `Stacks.EtaleCohomology.extensionByZeroIntegralTwist` of `ε` with the twist
`j_!(ε') ≫ (j_! σ_{V,*} ⟶ σ_* j_!)` of `j_! G'`. This is used in [Stacks, Tag 03VK] to compare
the Galois actions on `H²(C, j_! j^{-1} -)` and `H²(C, j_! -)`.

## Main results

* `Stacks.EtaleCohomology.extensionByZeroIntegralTwist_comp_map_of_restriction`.

## References

* [Stacks Project, Tag 03VK](https://stacks.math.columbia.edu/tag/03VK).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable (Λ : Type) [Ring Λ] {V Vb : Scheme.{u}} (j : V ⟶ Vb) [Etale j] [Mono j]
  (σV : V ⟶ V) (σ : Vb ⟶ Vb) [IsIntegralHom σ] (sq : IsPullback σV j j σ)

omit [Mono j] in
/-- **Extension by zero of a twist, compared through the restriction.** Let `l : j^{-1} G ⟶ G'`
intertwine the restriction of `ε : G ⟶ σ_* G` (through `j^{-1} σ_* ≅ σ_{V,*} j^{-1}`) with a twist
`ε' : G' ⟶ σ_{V,*} G'`. Then `j_! l` intertwines the extension by zero of `ε` with the twist
`j_!(ε') ≫ (j_! σ_{V,*} ⟶ σ_* j_!)` of `j_! G'`. -/
theorem extensionByZeroIntegralTwist_comp_map_of_restriction (G : EtaleModules.{u, 0} Λ Vb)
    (ε : G ⟶ (etaleModuleDirectImage.{u, 0} Λ σ).obj G) (G' : EtaleModules.{u, 0} Λ V)
    (ε' : G' ⟶ (etaleModuleDirectImage.{u, 0} Λ σV).obj G')
    (l : (etaleModuleRestriction.{u, 0} Λ j).obj G ⟶ G')
    (hl : (etaleModuleRestriction.{u, 0} Λ j).map ε ≫
        (restrictionIntegralDirectImageIso Λ j j σV σ sq).inv.app G ≫
          (etaleModuleDirectImage.{u, 0} Λ σV).map l = l ≫ ε') :
    extensionByZeroIntegralTwist Λ j σV σ sq G ε ≫
        (etaleModuleDirectImage.{u, 0} Λ σ).map ((etaleModuleExtensionByZero.{u, 0} Λ j).map l) =
      (etaleModuleExtensionByZero.{u, 0} Λ j).map l ≫
        ((etaleModuleExtensionByZero.{u, 0} Λ j).map ε' ≫
          extensionByZeroIntegralDirectImageMap Λ j j σV σ sq G') := by
  rw [extensionByZeroIntegralTwist, Category.assoc,
    ← extensionByZeroIntegralDirectImageMap_naturality, ← Functor.map_comp_assoc, Category.assoc,
    hl, Functor.map_comp_assoc]

end Stacks.EtaleCohomology

end
