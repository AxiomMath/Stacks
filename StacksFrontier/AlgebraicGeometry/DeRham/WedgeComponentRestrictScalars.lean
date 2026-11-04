module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorRestrictScalarsEpi
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafWorldBridge
public import StacksFrontier.AlgebraicGeometry.DeRham.CupProduct.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.CrystalsInQuasicoherentModules

/-!
# The wedge component over the base ring is the exterior multiplication, restricted

Let `φ : A ⟶ 𝒪_X` be a morphism of sheaves of commutative rings on a space, with `𝒪_X` the
structure sheaf of a ringed space `X`, and let `Ω = Ω_{𝒪_X/A}` be the sheaf of relative
differentials with a package of the three algebras of Stacks Section 17.21. Wedge multiplication
of differential forms is realized in two ways:

* over the base ring sheaf `A`, as `AlgebraicGeometry.SheafOfModules.exteriorProductComponent`,
  a morphism `Ωᵖ ⊗_A Ωᵠ ⟶ Ωᵖ⁺ᵠ` of sheaves of `A`-modules, the component of the wedge product of
  [Stacks, Tag 0FM2];
* over the structure sheaf, as `SheafOfModules.GradedAlgebra.mulSheaf` of the exterior algebra,
  a morphism `⋀ᵖΩ ⊗_{𝒪_X} ⋀ᵠΩ ⟶ ⋀^{p+q}Ω` of sheaves of `𝒪_X`-modules.

This file identifies them: the `A`-linear component factors as the lax comparison
`Ωᵖ ⊗_A Ωᵠ ⟶ (⋀ᵖΩ ⊗_{𝒪_X} ⋀ᵠΩ)|_A` followed by the restriction of scalars of the exterior
multiplication. The comparison is an epimorphism, so the two morphisms have the same image.

## Main results

* `AlgebraicGeometry.SheafOfModules.laxComparison_comp_restrictScalars_mulSheaf`: **the wedge
  component over `A` is the lax comparison followed by the restriction of scalars of the exterior
  multiplication.**
* `AlgebraicGeometry.SheafOfModules.imageSubobject_exteriorProductComponent`: **the two
  realizations of the wedge product have the same image.**

## References

* [Stacks Project, Tag 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
* [Stacks Project, Tag 0FM2](https://stacks.math.columbia.edu/tag/0FM2)
* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open scoped TensorProduct

universe u

namespace AlgebraicGeometry.SheafOfModules

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  (B : _root_.SheafOfModules.TensorExteriorSymmetricAlgebras
    (Opens.grothendieckTopology X.carrier) (moduleOfDifferentials.{u, u, u} φ))

/-! Sheaves of modules over a ring sheaf form an abelian category. Finding that at these binders
exceeds the default instance-synthesis budget, so the global instance is made a local one. -/
attribute [local instance] _root_.SheafOfModules.instAbelian

/-- **The lax comparison on a local pure tensor**: it carries the pure tensor of two local
sections over the base ring sheaf to their pure tensor over the structure sheaf. -/
theorem laxComparison_val_app_tensorSheafUnit
    (M N : _root_.SheafOfModules.{u}
      (Sheaf.toRingCat (Opens.grothendieckTopology X.carrier) X.sheaf))
    (U : (Opens X.carrier)ᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    (Stacks.SheafOfModules.TensorRestrictScalars.laxComparison A X.sheaf φ M N).val.app U
        ((PresheafOfModules.tensorSheafUnit
            ((_root_.SheafOfModules.restrictScalars (underlyingRingHom (φ := φ))).obj M)
            ((_root_.SheafOfModules.restrictScalars (underlyingRingHom (φ := φ))).obj N)).app U
          (x ⊗ₜ[A.obj.obj U] y)) =
      (PresheafOfModules.tensorSheafUnit M N).app U (x ⊗ₜ[X.sheaf.obj.obj U] y) :=
  Stacks.SheafOfModules.TensorRestrictScalars.laxComparison_toTensorSheafSection
    A X.sheaf φ M N U (x ⊗ₜ[A.obj.obj U] y)

/-- **The wedge component over the base ring is the restricted exterior multiplication**: the
component `exteriorProductComponent B p q : Ωᵖ ⊗_A Ωᵠ ⟶ Ωᵖ⁺ᵠ` equals the lax comparison
`Ωᵖ ⊗_A Ωᵠ ⟶ (⋀ᵖΩ ⊗_{𝒪_X} ⋀ᵠΩ)|_A` followed by the restriction of scalars along `φ` of the
exterior multiplication `⋀ᵖΩ ⊗_{𝒪_X} ⋀ᵠΩ ⟶ ⋀^{p+q}Ω`. -/
theorem laxComparison_comp_restrictScalars_mulSheaf (p q : ℕ) :
    Stacks.SheafOfModules.TensorRestrictScalars.laxComparison A X.sheaf φ
          (B.exteriorPower p) (B.exteriorPower q) ≫
        (_root_.SheafOfModules.restrictScalars (underlyingRingHom (φ := φ))).map
          (_root_.SheafOfModules.GradedAlgebra.mulSheaf B.exterior (p : ℤ) (q : ℤ)) =
      exteriorProductComponent B p q := by
  refine PresheafOfModules.tensorSheaf_hom_ext (Osharp := A) (F := deRhamTerm B p)
    (G := deRhamTerm B q) (Q := deRhamTerm B (p + q)) fun U x y => ?_
  refine Eq.trans ?_ (exteriorProductComponent_unit_apply B p q U x y).symm
  refine Eq.trans (congrArg
    ((_root_.SheafOfModules.GradedAlgebra.mulSheaf B.exterior (p : ℤ) (q : ℤ)).val.app U)
    (laxComparison_val_app_tensorSheafUnit (φ := φ) (B.exteriorPower p)
      (B.exteriorPower q) U x y)) ?_
  exact _root_.SheafOfModules.GradedAlgebra.mulSheaf_unit B.exterior (p : ℤ) (q : ℤ) U x y

/-- The image of the wedge component `exteriorProductComponent B p q` over the base ring equals
the image of the restriction of scalars along `φ` of the exterior multiplication
`⋀ᵖΩ ⊗_{𝒪_X} ⋀ᵠΩ ⟶ ⋀^{p+q}Ω`. -/
theorem imageSubobject_exteriorProductComponent (p q : ℕ) :
    Limits.imageSubobject (exteriorProductComponent B p q) =
      Limits.imageSubobject
        ((_root_.SheafOfModules.restrictScalars (underlyingRingHom (φ := φ))).map
          (_root_.SheafOfModules.GradedAlgebra.mulSheaf B.exterior (p : ℤ) (q : ℤ))) := by
  rw [← laxComparison_comp_restrictScalars_mulSheaf B p q]
  exact Stacks.CategoryTheory.Subobject.imageSubobject_epi_comp _
    (Stacks.SheafOfModules.TensorRestrictScalars.epi_laxComparison A X.sheaf φ
      (B.exteriorPower p) (B.exteriorPower q)) _

end AlgebraicGeometry.SheafOfModules

end
