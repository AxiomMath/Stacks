module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.MorphismWeaklyAssociated.SpaceRelativeEtaleInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullbackTensor

/-!
# Bourbaki's formula on an algebraic space

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`, let `F` be an
`𝒪_X`-module and `G` an `𝒪_Y`-module. Bourbaki's formula asserts that the weakly associated
points of `F ⊗_{𝒪_X} f^*G` are exactly the points of the relative weak assassin
`WeakAss_{X/Y}(F)` lying above weakly associated points of `G`.

## Main results

* `AlgebraicGeometry.Space.isWeaklyAssociatedPoint_tensor_modulePullback_iff`: the left-hand
  condition of Bourbaki's formula is invariant under an étale morphism.
* `AlgebraicGeometry.Space.isRelativeWeaklyAssociatedPoint_and_mem_modulePullback_iff`: so is
  the right-hand condition.
* `AlgebraicGeometry.Space.weaklyAssociatedPoints_tensor_modulePullback_eq_of_chart`:
  Bourbaki's formula, descended from a surjective étale chart on which it holds.

## Remark

Bourbaki's formula needs `F` to be flat over `Y`. For the closed immersion `Spec k ⟶ Spec k[t]`
with `F = 𝒪_X` and `G = 𝒪_Y`, the left-hand side is the point of `X`, while the right-hand side
is empty, since the image point is not weakly associated to `𝒪_Y`.

## References

* [Stacks Project, Tag 0CV1](https://stacks.math.columbia.edu/tag/0CV1)
* [Stacks Project, Tag 0CV0](https://stacks.math.columbia.edu/tag/0CV0)
* [Stacks Project, Tag 0CUZ](https://stacks.math.columbia.edu/tag/0CUZ)
* [Stacks Project, Tag 0CUU](https://stacks.math.columbia.edu/tag/0CUU)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 05DB](https://stacks.math.columbia.edu/tag/05DB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X X' Y : AlgebraicSpaces B S hS}

/-- The left-hand condition of Bourbaki's formula is invariant under an étale morphism of the
source: a point of `X'` is weakly associated to `φ^*F ⊗ (φ ≫ f)^*G` exactly when its image is
weakly associated to `F ⊗ f^*G`. -/
theorem isWeaklyAssociatedPoint_tensor_modulePullback_iff (φ : X' ⟶ X)
    (hφ : IsEtale B S hS φ.hom) (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    (G : Modules.{u, u} B S hS Y.1 Y.2) (x : points B S hS X'.1) :
    IsWeaklyAssociatedPoint B S hS X'
        ((modulePullback B S hS φ).obj F ⊗ (modulePullback B S hS (φ ≫ f)).obj G) x ↔
      IsWeaklyAssociatedPoint B S hS X (F ⊗ (modulePullback B S hS f).obj G)
        (pointsMap B S hS X'.1 φ.hom x) :=
  (isWeaklyAssociatedPoint_congr B S hS
      (modulePullbackTensorCompIso B S hS φ f F G) x).symm.trans
    (isWeaklyAssociatedPoint_modulePullback_iff B S hS φ hφ _ x)

/-- The right-hand condition of Bourbaki's formula is invariant under an étale morphism of the
source: a point of `X'` lies in `WeakAss_{X'/Y}(φ^*F)` above a weakly associated point of `G`
exactly when its image lies in `WeakAss_{X/Y}(F)` above a weakly associated point of `G`. -/
theorem isRelativeWeaklyAssociatedPoint_and_mem_modulePullback_iff (φ : X' ⟶ X)
    (hφ : IsEtale B S hS φ.hom) (f : X ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2)
    (G : Modules.{u, u} B S hS Y.1 Y.2) (x : points B S hS X'.1) :
    (IsRelativeWeaklyAssociatedPoint B S hS (φ ≫ f) ((modulePullback B S hS φ).obj F) x ∧
        IsWeaklyAssociatedPoint B S hS Y G (pointsMap B S hS X'.1 (φ ≫ f).hom x)) ↔
      (IsRelativeWeaklyAssociatedPoint B S hS f F (pointsMap B S hS X'.1 φ.hom x) ∧
        IsWeaklyAssociatedPoint B S hS Y G
          (pointsMap B S hS X.1 f.hom (pointsMap B S hS X'.1 φ.hom x))) :=
  and_congr (isRelativeWeaklyAssociatedPoint_modulePullback_iff B S hS φ hφ f F x)
    (by rw [show (φ ≫ f).hom = φ.hom ≫ f.hom from rfl, pointsMap_comp, Function.comp_apply])

/-- **The étale-localization step of Bourbaki's formula on an algebraic space.** For
`f : X ⟶ Y` a morphism of algebraic spaces over a scheme `S`, the weakly associated points of
`F ⊗_{𝒪_X} f^*G` are the points of the relative weak assassin `WeakAss_{X/Y}(F)` lying above
weakly associated points of `G`, *granted* the same formula on a surjective étale chart. -/
theorem weaklyAssociatedPoints_tensor_modulePullback_eq_of_chart (f : X ⟶ Y)
    (F : Modules.{u, u} B S hS X.1 X.2) (G : Modules.{u, u} B S hS Y.1 Y.2)
    (φ : X' ⟶ X) (hφ : IsEtale B S hS φ.hom)
    (hsurj : Function.Surjective (pointsMap B S hS X'.1 φ.hom))
    (hchart : ∀ x : points B S hS X'.1,
      IsWeaklyAssociatedPoint B S hS X'
          ((modulePullback B S hS φ).obj F ⊗ (modulePullback B S hS (φ ≫ f)).obj G) x ↔
        (IsRelativeWeaklyAssociatedPoint B S hS (φ ≫ f) ((modulePullback B S hS φ).obj F) x ∧
          IsWeaklyAssociatedPoint B S hS Y G (pointsMap B S hS X'.1 (φ ≫ f).hom x))) :
    weaklyAssociatedPoints B S hS X (F ⊗ (modulePullback B S hS f).obj G) =
      {x | x ∈ relativeWeaklyAssociatedPoints B S hS f F ∧
        pointsMap B S hS X.1 f.hom x ∈ weaklyAssociatedPoints B S hS Y G} := by
  ext x
  obtain ⟨y, rfl⟩ := hsurj x
  simp only [Set.mem_ofPred_eq]
  rw [← isWeaklyAssociatedPoint_tensor_modulePullback_iff B S hS φ hφ f F G y, hchart y,
    isRelativeWeaklyAssociatedPoint_and_mem_modulePullback_iff B S hS φ hφ f F G y]

end AlgebraicGeometry.Space

end
