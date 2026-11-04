module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportSmoothModelNatural

/-!
# Extension by zero of an equivariant structure, coefficients in any ring

Let `Λ` be a ring, `j : V ⟶ V̄` an étale monomorphism (an open immersion) and `σ : V̄ ⟶ V̄` an
integral morphism with `σ^{-1}(V) = V`, that is, a cartesian square `σ_V ≫ j = j ≫ σ`.  A sheaf
`G` of `Λ`-modules on `V̄` with a map `ε : G ⟶ σ_* G` induces a map
`j_! j^{-1} G ⟶ σ_*(j_! j^{-1} G)`: the restriction of `ε`, the identification
`j^{-1} σ_* ≅ σ_{V,*} j^{-1}` (`Stacks.EtaleCohomology.restrictionIntegralDirectImageIso`), and the
canonical map `j_! σ_{V,*} ⟶ σ_* j_!`
(`Stacks.EtaleCohomology.extensionByZeroIntegralDirectImageMap`).  The counit `j_! j^{-1} G ⟶ G`
intertwines it with `ε`.

This is the noncommutative-coefficient form of the construction of Step 9 of the proof of
[Stacks, Tag 03UG] (the action of a deck transformation on `j_! A`); the proofs do not use
commutativity of `Λ`.  In [Stacks, Tag 03VK] it relates the Galois action on
`H²(C, j_!(F|_U))`, `C` the smooth projective model of the curve, to the Galois action on
`H²(C, j_! j^{-1} q^{-1}(j̄_! F))`.

## Main definitions

* `Stacks.EtaleCohomology.extensionByZeroIntegralTwist`.

## Main results

* `Stacks.EtaleCohomology.extensionByZeroIntegralTwist_comp_counit`.
* `Stacks.EtaleCohomology.extensionByZeroIntegralTwist_naturality`.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Step 9.
* [Stacks Project, Tag 03VK](https://stacks.math.columbia.edu/tag/03VK).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable (Λ : Type) [Ring Λ] {V Vb : Scheme.{u}} (j : V ⟶ Vb) [Etale j] [Mono j]
  (σV : V ⟶ V) (σ : Vb ⟶ Vb) [IsIntegralHom σ] (sq : IsPullback σV j j σ)

/-- **The extension by zero of a map `ε : G ⟶ σ_* G`**, `Λ` any ring: the map
`j_! j^{-1} G ⟶ σ_*(j_! j^{-1} G)` given by `j_!` of the restriction of `ε` through
`j^{-1} σ_* ≅ σ_{V,*} j^{-1}`, followed by the canonical map `j_! σ_{V,*} ⟶ σ_* j_!`. -/
def extensionByZeroIntegralTwist (G : EtaleModules.{u, 0} Λ Vb)
    (ε : G ⟶ (etaleModuleDirectImage.{u, 0} Λ σ).obj G) :
    (etaleModuleExtensionByZero.{u, 0} Λ j).obj ((etaleModuleRestriction.{u, 0} Λ j).obj G) ⟶
      (etaleModuleDirectImage.{u, 0} Λ σ).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ j).obj ((etaleModuleRestriction.{u, 0} Λ j).obj G)) :=
  (etaleModuleExtensionByZero.{u, 0} Λ j).map ((etaleModuleRestriction.{u, 0} Λ j).map ε ≫
      (restrictionIntegralDirectImageIso Λ j j σV σ sq).inv.app G) ≫
    extensionByZeroIntegralDirectImageMap Λ j j σV σ sq ((etaleModuleRestriction.{u, 0} Λ j).obj G)

omit [Mono j] in
/-- **The counit intertwines the extension by zero of `ε` with `ε`.** -/
theorem extensionByZeroIntegralTwist_comp_counit (G : EtaleModules.{u, 0} Λ Vb)
    (ε : G ⟶ (etaleModuleDirectImage.{u, 0} Λ σ).obj G) :
    extensionByZeroIntegralTwist Λ j σV σ sq G ε ≫
        (etaleModuleDirectImage.{u, 0} Λ σ).map
          ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j).counit.app G) =
      (etaleModuleExtensionByZeroAdj.{u, 0} Λ j).counit.app G ≫ ε := by
  apply ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  have hext : (etaleModuleExtensionByZeroAdj.{u, 0} Λ j).unit.app
        ((etaleModuleDirectImage.{u, 0} Λ σV).obj ((etaleModuleRestriction.{u, 0} Λ j).obj G)) ≫
      (etaleModuleRestriction.{u, 0} Λ j).map
        (extensionByZeroIntegralDirectImageMap Λ j j σV σ sq
          ((etaleModuleRestriction.{u, 0} Λ j).obj G)) =
      (etaleModuleDirectImage.{u, 0} Λ σV).map
          ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j).unit.app
            ((etaleModuleRestriction.{u, 0} Λ j).obj G)) ≫
        (restrictionIntegralDirectImageIso Λ j j σV σ sq).hom.app
          ((etaleModuleExtensionByZero.{u, 0} Λ j).obj
            ((etaleModuleRestriction.{u, 0} Λ j).obj G)) :=
    (Adjunction.homEquiv_unit _ _ _ _).symm.trans (Equiv.apply_symm_apply _ _)
  have hu := (etaleModuleExtensionByZeroAdj.{u, 0} Λ j).unit.naturality
    ((etaleModuleRestriction.{u, 0} Λ j).map ε ≫
      (restrictionIntegralDirectImageIso Λ j j σV σ sq).inv.app G)
  have hn := (restrictionIntegralDirectImageIso Λ j j σV σ sq).hom.naturality
    ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j).counit.app G)
  have ht₁ := (etaleModuleExtensionByZeroAdj.{u, 0} Λ j).right_triangle_components G
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at hu hn ht₁
  rw [reassoc_of% ht₁, extensionByZeroIntegralTwist, Functor.map_comp, ← Category.assoc,
    ← Category.assoc, ← hu, Category.assoc, Category.assoc, reassoc_of% hext, ← hn,
    ← Functor.map_comp_assoc, ht₁, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.assoc, Iso.inv_hom_id_app]
  exact Category.comp_id _

omit [Mono j] in
/-- **Naturality of `extensionByZeroIntegralTwist`** in the pair `(G, ε)`. -/
theorem extensionByZeroIntegralTwist_naturality {G G' : EtaleModules.{u, 0} Λ Vb}
    (ε : G ⟶ (etaleModuleDirectImage.{u, 0} Λ σ).obj G)
    (ε' : G' ⟶ (etaleModuleDirectImage.{u, 0} Λ σ).obj G') (x : G ⟶ G')
    (hx : x ≫ ε' = ε ≫ (etaleModuleDirectImage.{u, 0} Λ σ).map x) :
    (etaleModuleExtensionByZero.{u, 0} Λ j).map ((etaleModuleRestriction.{u, 0} Λ j).map x) ≫
        extensionByZeroIntegralTwist Λ j σV σ sq G' ε' =
      extensionByZeroIntegralTwist Λ j σV σ sq G ε ≫ (etaleModuleDirectImage.{u, 0} Λ σ).map
        ((etaleModuleExtensionByZero.{u, 0} Λ j).map
          ((etaleModuleRestriction.{u, 0} Λ j).map x)) := by
  have hi := (restrictionIntegralDirectImageIso Λ j j σV σ sq).inv.naturality x
  dsimp only [Functor.comp_obj, Functor.comp_map] at hi
  have key : (etaleModuleRestriction.{u, 0} Λ j).map x ≫
      (etaleModuleRestriction.{u, 0} Λ j).map ε' ≫
        (restrictionIntegralDirectImageIso Λ j j σV σ sq).inv.app G' =
      ((etaleModuleRestriction.{u, 0} Λ j).map ε ≫
          (restrictionIntegralDirectImageIso Λ j j σV σ sq).inv.app G) ≫
        (etaleModuleDirectImage.{u, 0} Λ σV).map ((etaleModuleRestriction.{u, 0} Λ j).map x) := by
    rw [← Functor.map_comp_assoc, hx, Functor.map_comp_assoc, hi, Category.assoc]
  simp only [extensionByZeroIntegralTwist, Category.assoc]
  rw [← Functor.map_comp_assoc, key, Functor.map_comp_assoc,
    extensionByZeroIntegralDirectImageMap_naturality Λ j j σV σ sq]

end Stacks.EtaleCohomology

end
