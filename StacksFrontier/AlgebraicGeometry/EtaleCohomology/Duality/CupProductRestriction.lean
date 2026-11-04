module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleExtForgetPullback

/-!
# Restriction of étale cohomology with constant coefficients is multiplicative

Let `g : Y ⟶ X` be a morphism of schemes and `Λ` a commutative ring. Étale cohomology with
coefficients in the constant sheaf, `Hⁱ(X, Λ) = Ext^i_Λ(Λ_X, Λ_X)`, restricts along `g`: apply the
exact inverse image `g^{-1}` to an `Ext` class and conjugate by the comparison `Λ_Y ≅ g^{-1} Λ_X`.
Since `g^{-1}` is a functor, this restriction is compatible with the Yoneda product, which is the
cup product: `g^*(x ∪ y) = g^* x ∪ g^* y`.

## Main definitions

* `Stacks.EtaleCohomology.constantExtRestriction`: `g^* : Ext^i(Λ_X, Λ_X) →+ Ext^i(Λ_Y, Λ_Y)`.

## Main results

* `Stacks.EtaleCohomology.constantExtRestriction_comp`: `g^*(x ∘ y) = g^* x ∘ g^* y`.
* `Stacks.EtaleCohomology.constantExtRestriction_eq`: `g^*` is the restriction
  `Stacks.EtaleCohomology.etaleModuleExtRestriction` followed by the comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology

variable (Λ : Type) [CommRing Λ] {X Y : Scheme.{u}} (g : Y ⟶ X)

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

/-- The comparison `Λ_Y ≅ g^{-1} Λ_X` of constant sheaves. -/
abbrev constantInverseImageIso :
    Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ Y.smallEtaleTopology ≅
      (etaleModuleInverseImage.{u, 0} Λ g).obj
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology) :=
  ((etaleModuleInverseImageConstantIso.{u, 0} Λ g).app (ModuleCat.of Λ (ULift.{u + 1} Λ))).symm

/-- **Restriction of `Hⁱ(X, Λ) = Ext^i(Λ_X, Λ_X)` along `g : Y ⟶ X`**: apply the exact inverse
image and conjugate by `Λ_Y ≅ g^{-1} Λ_X`. -/
def constantExtRestriction (i : ℕ) :
    Ext (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology)
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology) i →+
      Ext (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ Y.smallEtaleTopology)
        (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ Y.smallEtaleTopology) i where
  toFun a := ((Ext.mk₀ (constantInverseImageIso Λ g).hom).comp
      (a.mapExactFunctor (etaleModuleInverseImage.{u, 0} Λ g)) (zero_add i)).comp
    (Ext.mk₀ (constantInverseImageIso Λ g).inv) (add_zero i)
  map_zero' := by simp
  map_add' a b := by simp [Ext.mapExactFunctor_add, Ext.comp_add, Ext.add_comp]

/-- `g^* a` is the composite `Λ_Y ≅ g^{-1} Λ_X`, then `g^{-1} a`, then `g^{-1} Λ_X ≅ Λ_Y`. -/
theorem constantExtRestriction_apply {i : ℕ}
    (a : Ext (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology)
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology) i) :
    constantExtRestriction Λ g i a = ((Ext.mk₀ (constantInverseImageIso Λ g).hom).comp
      (a.mapExactFunctor (etaleModuleInverseImage.{u, 0} Λ g)) (zero_add i)).comp
        (Ext.mk₀ (constantInverseImageIso Λ g).inv) (add_zero i) :=
  rfl

/-- `g^*` is the restriction `etaleModuleExtRestriction` followed by the comparison
`g^{-1} Λ_X ≅ Λ_Y`. -/
theorem constantExtRestriction_eq {i : ℕ}
    (a : Ext (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology)
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology) i) :
    constantExtRestriction Λ g i a = (etaleModuleExtRestriction Λ g _ i a).comp
        (Ext.mk₀ (constantInverseImageIso Λ g).inv) (add_zero i) :=
  rfl

/-- **Restriction is multiplicative**: `g^*(x ∘ y) = g^* x ∘ g^* y` for the Yoneda product on
`Ext^*(Λ_X, Λ_X)`, which is the cup product. -/
theorem constantExtRestriction_comp {a b c : ℕ}
    (x : Ext (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology)
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology) a)
    (y : Ext (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology)
      (Stacks.Cohomology.GlobalSections.constantModuleSheaf Λ X.smallEtaleTopology) b)
    (h : a + b = c) :
    constantExtRestriction Λ g c (x.comp y h) =
      (constantExtRestriction Λ g a x).comp (constantExtRestriction Λ g b y) h := by
  set H := Ext.mk₀ (constantInverseImageIso Λ g).hom
  set I := Ext.mk₀ (constantInverseImageIso Λ g).inv
  set x' := x.mapExactFunctor (etaleModuleInverseImage.{u, 0} Λ g)
  set y' := y.mapExactFunctor (etaleModuleInverseImage.{u, 0} Λ g)
  have hIH : I.comp ((H.comp y' (zero_add b)).comp I (add_zero b)) (zero_add b) =
      y'.comp I (add_zero b) := by
    rw [Ext.comp_assoc_of_third_deg_zero, ← Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀,
      Iso.inv_hom_id, Ext.mk₀_id_comp]
  rw [constantExtRestriction_apply, constantExtRestriction_apply, constantExtRestriction_apply,
    Ext.mapExactFunctor_comp]
  symm
  rw [Ext.comp_assoc_of_second_deg_zero, hIH,
    Ext.comp_assoc H x' (y'.comp I (add_zero b)) (zero_add a) h (by omega),
    ← Ext.comp_assoc_of_third_deg_zero x' y' I h,
    ← Ext.comp_assoc H (x'.comp y' h) I (zero_add c) (add_zero c) (by omega)]

end Stacks.EtaleCohomology

end
