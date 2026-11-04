module

public import StacksFrontier.Algebra.Homology.DerivedHomologyLinear
public import StacksFrontier.RingTheory.LocalCohomology.LocalizationTriangle.CechConeExact

/-!
# The long exact sequence of derived sections on the complement is natural and linear

A short exact sequence `S` of `R`-modules gives a distinguished triangle
`Stacks.LocalCohomology.cechComplementTriangle` of derived sections on `U = Spec R ∖ V(I)`, and
hence a long exact sequence of cohomology. This file proves two properties of it.

* **Naturality in the short exact sequence**: a morphism `S₁ ⟶ S₂` of short exact sequences
  induces a morphism of the two triangles, hence a commutative square relating the two connecting
  maps.
* **Linearity in the module**: multiplication by a scalar on the module induces multiplication by
  that scalar on every cohomology group of derived sections. In particular a module annihilated
  by a scalar has all its derived sections annihilated by that scalar.

## Main definitions

* `Stacks.LocalCohomology.cechComplementTriangleMap` — the morphism of triangles of derived
  sections induced by a morphism of short exact sequences of modules.

## Main results

* `Stacks.LocalCohomology.cechComplementδ_naturality` — **the connecting map of the long exact
  sequence is natural in the short exact sequence.**
* `Stacks.LocalCohomology.homologyComplement_map_smul` — derived sections on `U` are linear in the
  module in every degree.
* `Stacks.LocalCohomology.smul_homologyComplement_eq_zero` — a module annihilated by a scalar has
  all of its derived sections on `U` annihilated by that scalar.

## References

* [Stacks Project, Tag 0A6R](https://stacks.math.columbia.edu/tag/0A6R)
* [Stacks Project, Tag 0EII](https://stacks.math.columbia.edu/tag/0EII)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance] HasDerivedCategory.standard

universe v u

namespace Stacks.LocalCohomology

variable {R : Type u} [CommRing R] {r : ℕ} (f : Fin r → R)

/-! ### Naturality of the triangle and of its connecting map -/

/-- **The morphism of triangles of derived sections on `U` induced by a morphism of short exact
sequences of modules.** The triangle of
`Stacks.LocalCohomology.cechComplementTriangle` is `DerivedCategory.triangleOfSES` of the image of
the sequence under the cone of the Čech augmentation, so this is Mathlib's
`DerivedCategory.triangleOfSES.map` applied to the image of the morphism. -/
def cechComplementTriangleMap {S₁ S₂ : ShortComplex (ModuleCat.{max u v} R)}
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) :
    cechComplementTriangle.{v} f S₁ h₁ ⟶ cechComplementTriangle.{v} f S₂ h₂ :=
  DerivedCategory.triangleOfSES.map (shortExact_map_cechConeFunctor.{v} f S₁ h₁)
    (shortExact_map_cechConeFunctor.{v} f S₂ h₂)
    ((cechConeFunctor.{v} f).mapShortComplex.map φ)

/-- The first component of the morphism of triangles is derived sections of the first component of
the morphism of short exact sequences. -/
theorem cechComplementTriangleMap_hom₁ {S₁ S₂ : ShortComplex (ModuleCat.{max u v} R)}
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) :
    (cechComplementTriangleMap.{v} f h₁ h₂ φ).hom₁ = (cechComplementFunctor.{v} f).map φ.τ₁ :=
  rfl

/-- The third component of the morphism of triangles is derived sections of the third component of
the morphism of short exact sequences. -/
theorem cechComplementTriangleMap_hom₃ {S₁ S₂ : ShortComplex (ModuleCat.{max u v} R)}
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) :
    (cechComplementTriangleMap.{v} f h₁ h₂ φ).hom₃ = (cechComplementFunctor.{v} f).map φ.τ₃ :=
  rfl

/-- **The connecting map of the long exact sequence of derived sections on `U` is natural in the
short exact sequence.** For a morphism of short exact sequences of modules, the connecting map of
the target sequence applied to the image of a class is the image under the first component of the
connecting map of the source sequence. -/
theorem cechComplementδ_naturality {S₁ S₂ : ShortComplex (ModuleCat.{max u v} R)}
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (φ : S₁ ⟶ S₂) (n₀ n₁ : ℤ) (h : n₀ + 1 = n₁)
    (y : (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) n₀).obj
      ((cechComplementFunctor.{v} f).obj S₁.X₃)) :
    DerivedCategory.HomologySequence.δ (cechComplementTriangle.{v} f S₂ h₂) n₀ n₁ h
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) n₀).map
          ((cechComplementFunctor.{v} f).map φ.τ₃) y) =
      (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) n₁).map
        ((cechComplementFunctor.{v} f).map φ.τ₁)
        (DerivedCategory.HomologySequence.δ (cechComplementTriangle.{v} f S₁ h₁) n₀ n₁ h y) :=
  (ConcreteCategory.congr_hom
    (Stacks.HomologyLinear.homologySequenceδ_naturality
      (cechComplementTriangleMap.{v} f h₁ h₂ φ) n₀ n₁ h) y).symm

/-! ### Linearity in the module -/

/-- The cone of the Čech augmentation is a linear functor of the module. -/
instance cechConeFunctor_linear : Functor.Linear R (cechConeFunctor.{v} f) where
  map_smul g a := cechConeFunctor_map_smul.{v} f a g

/-- Derived sections on `U` are a linear functor of the module. -/
instance cechComplementFunctor_linear : Functor.Linear R (cechComplementFunctor.{v} f) :=
  inferInstanceAs (Functor.Linear R (cechConeFunctor.{v} f ⋙ DerivedCategory.Q))

/-- Derived sections on `U` are an additive functor of the module. -/
instance cechComplementFunctor_additive : (cechComplementFunctor.{v} f).Additive :=
  inferInstanceAs (cechConeFunctor.{v} f ⋙ DerivedCategory.Q).Additive

/-- **The cohomology of derived sections on `U` is linear in the module.** -/
theorem homologyComplement_map_smul (i : ℤ) {M N : ModuleCat.{max u v} R} (a : R) (g : M ⟶ N) :
    (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).map
        ((cechComplementFunctor.{v} f).map (a • g)) =
      a • (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).map
        ((cechComplementFunctor.{v} f).map g) := by
  rw [(cechComplementFunctor.{v} f).map_smul a g,
    Stacks.HomologyLinear.derivedHomologyMap_smul i ((cechComplementFunctor.{v} f).map g) a]

/-- Multiplication by a scalar on the module induces multiplication by that scalar on the
cohomology of derived sections on `U`. -/
theorem homologyComplement_map_smul_id_apply (i : ℤ) (N : ModuleCat.{max u v} R) (a : R)
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj
      ((cechComplementFunctor.{v} f).obj N)) :
    (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).map
        ((cechComplementFunctor.{v} f).map (a • 𝟙 N)) x = a • x := by
  rw [homologyComplement_map_smul.{v} f i a (𝟙 N),
    CategoryTheory.Functor.map_id (cechComplementFunctor.{v} f) N,
    CategoryTheory.Functor.map_id (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i)
      ((cechComplementFunctor.{v} f).obj N)]
  rfl

/-- **A module annihilated by a scalar has all of its derived sections on `U` annihilated by that
scalar.** -/
theorem smul_homologyComplement_eq_zero (i : ℤ) (N : ModuleCat.{max u v} R) (a : R)
    (hN : ∀ y : N, a • y = 0)
    (x : (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i).obj
      ((cechComplementFunctor.{v} f).obj N)) : a • x = 0 := by
  have h0 : (a • 𝟙 N) = (0 : N ⟶ N) := ModuleCat.hom_ext (LinearMap.ext fun y ↦ hN y)
  rw [← homologyComplement_map_smul_id_apply.{v} f i N a x, h0,
    CategoryTheory.Functor.map_zero (cechComplementFunctor.{v} f) N N,
    CategoryTheory.Functor.map_zero (DerivedCategory.homologyFunctor (ModuleCat.{max u v} R) i)
      ((cechComplementFunctor.{v} f).obj N) ((cechComplementFunctor.{v} f).obj N)]
  rfl

end Stacks.LocalCohomology

end
