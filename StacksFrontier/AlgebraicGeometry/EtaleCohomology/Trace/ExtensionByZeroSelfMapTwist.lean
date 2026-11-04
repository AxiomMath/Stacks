module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ExtensionByZeroIntegralDirectImage

/-!
# Extension by zero of an equivariant structure

Let `j : V ⟶ V̄` be an étale monomorphism (an open immersion) and `σ : V̄ ⟶ V̄` an integral
morphism (an automorphism, in the application) with `σ^{-1}(V) = V`, that is, a cartesian square
`σ_V ≫ j = j ≫ σ`.  A sheaf `G` on `V̄` with a map `ε : G ⟶ σ_* G` induces a map
`j_! j^{-1} G ⟶ σ_*(j_! j^{-1} G)`: the restriction of `ε`, the identification
`j^{-1} σ_* ≅ σ_{V,*} j^{-1}`, and the canonical map `j_! σ_{V,*} ⟶ σ_* j_!`.  The counit
`j_! j^{-1} G ⟶ G` intertwines it with `ε`.

In Step 9 of the proof of [Stacks, Tag 03UG] this is the action of the deck transformation on
`j_! A`, for `j : V ⟶ V̄` the inclusion of the Galois cover into its compactification, and the
counit is the map `j_! A ⟶ A` of the open/closed sequence.

## Main definitions

* `Stacks.EtaleCohomology.extensionByZeroTwist`.

## Main results

* `Stacks.EtaleCohomology.extensionByZeroTwist_comp_counit`.
* `Stacks.EtaleCohomology.extensionByZeroTwist_naturality`,
  `Stacks.EtaleCohomology.extensionByZeroDirectImageMap_naturality`.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG), Step 9.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

variable (Λ : Type) [CommRing Λ] {V Vb : Scheme.{u}} (j : V ⟶ Vb) [Etale j] [Mono j]
  (σV : V ⟶ V) (σ : Vb ⟶ Vb) [IsIntegralHom σ] (sq : IsPullback σV j j σ)

/-- **The extension by zero of a map `ε : G ⟶ σ_* G`**: the map
`j_! j^{-1} G ⟶ σ_*(j_! j^{-1} G)` given by `j_!` of the restriction of `ε` through
`j^{-1} σ_* ≅ σ_{V,*} j^{-1}`, followed by the canonical map `j_! σ_{V,*} ⟶ σ_* j_!`. -/
def extensionByZeroTwist (G : EtaleModules.{u, 0} Λ Vb)
    (ε : G ⟶ (etaleModuleDirectImage.{u, 0} Λ σ).obj G) :
    (etaleModuleExtensionByZero.{u, 0} Λ j).obj ((etaleModuleRestriction.{u, 0} Λ j).obj G) ⟶
      (etaleModuleDirectImage.{u, 0} Λ σ).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ j).obj ((etaleModuleRestriction.{u, 0} Λ j).obj G)) :=
  (etaleModuleExtensionByZero.{u, 0} Λ j).map ((etaleModuleRestriction.{u, 0} Λ j).map ε ≫
      (restrictionDirectImageIso Λ j j σV σ sq).inv.app G) ≫
    extensionByZeroDirectImageMap Λ j j σV σ sq ((etaleModuleRestriction.{u, 0} Λ j).obj G)

omit [Mono j] in
/-- **The counit intertwines the extension by zero of `ε` with `ε`.** -/
theorem extensionByZeroTwist_comp_counit (G : EtaleModules.{u, 0} Λ Vb)
    (ε : G ⟶ (etaleModuleDirectImage.{u, 0} Λ σ).obj G) :
    extensionByZeroTwist Λ j σV σ sq G ε ≫
        (etaleModuleDirectImage.{u, 0} Λ σ).map
          ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j).counit.app G) =
      (etaleModuleExtensionByZeroAdj.{u, 0} Λ j).counit.app G ≫ ε := by
  apply ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j).homEquiv _ _).injective
  simp only [Adjunction.homEquiv_unit, Functor.map_comp]
  have hext : (etaleModuleExtensionByZeroAdj.{u, 0} Λ j).unit.app
        ((etaleModuleDirectImage.{u, 0} Λ σV).obj ((etaleModuleRestriction.{u, 0} Λ j).obj G)) ≫
      (etaleModuleRestriction.{u, 0} Λ j).map
        (extensionByZeroDirectImageMap Λ j j σV σ sq ((etaleModuleRestriction.{u, 0} Λ j).obj G)) =
      (etaleModuleDirectImage.{u, 0} Λ σV).map
          ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j).unit.app
            ((etaleModuleRestriction.{u, 0} Λ j).obj G)) ≫
        (restrictionDirectImageIso Λ j j σV σ sq).hom.app
          ((etaleModuleExtensionByZero.{u, 0} Λ j).obj
            ((etaleModuleRestriction.{u, 0} Λ j).obj G)) :=
    (Adjunction.homEquiv_unit _ _ _ _).symm.trans (Equiv.apply_symm_apply _ _)
  have hu := (etaleModuleExtensionByZeroAdj.{u, 0} Λ j).unit.naturality
    ((etaleModuleRestriction.{u, 0} Λ j).map ε ≫
      (restrictionDirectImageIso Λ j j σV σ sq).inv.app G)
  have hn := (restrictionDirectImageIso Λ j j σV σ sq).hom.naturality
    ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j).counit.app G)
  have ht₁ := (etaleModuleExtensionByZeroAdj.{u, 0} Λ j).right_triangle_components G
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at hu hn ht₁
  rw [reassoc_of% ht₁, extensionByZeroTwist, Functor.map_comp, ← Category.assoc,
    ← Category.assoc, ← hu, Category.assoc, Category.assoc, reassoc_of% hext, ← hn,
    ← Functor.map_comp_assoc, ht₁, CategoryTheory.Functor.map_id, Category.id_comp,
    Category.assoc, Iso.inv_hom_id_app]
  exact Category.comp_id _

/-- **Naturality of the canonical map `j_!(f_* M) ⟶ f̄_*(j'_! M)`** in `M`. -/
theorem extensionByZeroDirectImageMap_naturality {V' Vb' : Scheme.{u}} (j' : V' ⟶ Vb') [Etale j']
    [Mono j'] (f : V' ⟶ V) (fb : Vb' ⟶ Vb) [IsIntegralHom fb] (sq' : IsPullback f j' j fb)
    {M M' : EtaleModules.{u, 0} Λ V'} (x : M ⟶ M') :
    (etaleModuleExtensionByZero.{u, 0} Λ j).map ((etaleModuleDirectImage.{u, 0} Λ f).map x) ≫
        extensionByZeroDirectImageMap Λ j j' f fb sq' M' =
      extensionByZeroDirectImageMap Λ j j' f fb sq' M ≫
        (etaleModuleDirectImage.{u, 0} Λ fb).map
          ((etaleModuleExtensionByZero.{u, 0} Λ j').map x) := by
  apply ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j).homEquiv _ _).injective
  have hext : ∀ N : EtaleModules.{u, 0} Λ V',
      ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j).homEquiv _ _)
        (extensionByZeroDirectImageMap Λ j j' f fb sq' N) =
      (etaleModuleDirectImage.{u, 0} Λ f).map
          ((etaleModuleExtensionByZeroAdj.{u, 0} Λ j').unit.app N) ≫
        (restrictionDirectImageIso Λ j j' f fb sq').hom.app
          ((etaleModuleExtensionByZero.{u, 0} Λ j').obj N) := fun N => Equiv.apply_symm_apply _ _
  rw [Adjunction.homEquiv_naturality_left, hext, Adjunction.homEquiv_naturality_right, hext]
  have hu := (etaleModuleExtensionByZeroAdj.{u, 0} Λ j').unit.naturality x
  have hn := (restrictionDirectImageIso Λ j j' f fb sq').hom.naturality
    ((etaleModuleExtensionByZero.{u, 0} Λ j').map x)
  dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map] at hu hn
  rw [Category.assoc, ← hn, ← Functor.map_comp_assoc, ← Functor.map_comp_assoc, hu]

/-- **Naturality of `extensionByZeroTwist`** in the pair `(G, ε)`. -/
theorem extensionByZeroTwist_naturality {G G' : EtaleModules.{u, 0} Λ Vb}
    (ε : G ⟶ (etaleModuleDirectImage.{u, 0} Λ σ).obj G)
    (ε' : G' ⟶ (etaleModuleDirectImage.{u, 0} Λ σ).obj G') (x : G ⟶ G')
    (hx : x ≫ ε' = ε ≫ (etaleModuleDirectImage.{u, 0} Λ σ).map x) :
    (etaleModuleExtensionByZero.{u, 0} Λ j).map ((etaleModuleRestriction.{u, 0} Λ j).map x) ≫
        extensionByZeroTwist Λ j σV σ sq G' ε' =
      extensionByZeroTwist Λ j σV σ sq G ε ≫ (etaleModuleDirectImage.{u, 0} Λ σ).map
        ((etaleModuleExtensionByZero.{u, 0} Λ j).map
          ((etaleModuleRestriction.{u, 0} Λ j).map x)) := by
  have hi := (restrictionDirectImageIso Λ j j σV σ sq).inv.naturality x
  dsimp only [Functor.comp_obj, Functor.comp_map] at hi
  have key : (etaleModuleRestriction.{u, 0} Λ j).map x ≫
      (etaleModuleRestriction.{u, 0} Λ j).map ε' ≫
        (restrictionDirectImageIso Λ j j σV σ sq).inv.app G' =
      ((etaleModuleRestriction.{u, 0} Λ j).map ε ≫
        (restrictionDirectImageIso Λ j j σV σ sq).inv.app G) ≫
        (etaleModuleDirectImage.{u, 0} Λ σV).map ((etaleModuleRestriction.{u, 0} Λ j).map x) := by
    rw [← Functor.map_comp_assoc, hx, Functor.map_comp_assoc, hi, Category.assoc]
  simp only [extensionByZeroTwist, Category.assoc]
  rw [← Functor.map_comp_assoc, key, Functor.map_comp_assoc,
    extensionByZeroDirectImageMap_naturality Λ j j σV σ sq]

end Stacks.EtaleCohomology

end
