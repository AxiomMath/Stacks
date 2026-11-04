module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingStructureMorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingTwoFibreProduct
public import StacksFrontier.AlgebraicGeometry.Stacks.LimitPreservingTwoFibreProductObjects
public import StacksFrontier.AlgebraicGeometry.Stacks.SecondDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.Representability

/-!
# The site and the self-product of a limit preserving category fibred in groupoids

The big fppf site of `S`, viewed as a category fibred in groupoids over itself by the identity
functor, is limit preserving: its fibre over an object is equivalent to the one-object category,
so the comparison out of the colimit over the stages of an inverse system is an equivalence. The
self-product `𝒳 × 𝒳` of a limit preserving `𝒳` is therefore limit preserving, and its structure
morphism to the site is limit preserving on objects.

## Main results

* `AlgebraicGeometry.Stack.isLimitPreserving_terminalCFG`: the site is limit preserving.
* `AlgebraicGeometry.Stack.isLimitPreserving_product`: `𝒳 × 𝒳` is limit preserving when `𝒳` is.
* `AlgebraicGeometry.Stack.isLimitPreservingOnObjects_toTerminalCFG_product`: the structure
  morphism of `𝒳 × 𝒳` is limit preserving on objects when `𝒳` is limit preserving.

## Implementation notes

The product `𝒳 × 𝒳` of `CategoryTheory.CatFiberedInGroupoids.product` is the 2-fibre product of
`𝒳` with itself over the site, so the two product statements are Stacks 07XM read at
`AlgebraicGeometry.Stack.terminalCFG`, whose own limit preservation is the input proved here.

For the identity functor the three descent conditions of Stacks 07XL are immediate: an object of
a fibre is an object of the site equal to the base, and two morphisms of the site lying over one
and the same morphism through the identity functor are equal, so the stage asked for by each
condition is the given one and the index category need only be nonempty. The conditions are used
rather than the colimit itself because they mention no colimit.

## References

* [Stacks Project, Tag 07XL](https://stacks.math.columbia.edu/tag/07XL)
* [Stacks Project, Tag 07XM](https://stacks.math.columbia.edu/tag/07XM)
* [Stacks Project, Tag 06CU](https://stacks.math.columbia.edu/tag/06CU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Stack

universe u v w uC vC vI wI

section Identity

variable {𝒞 : Type uC} [Category.{vC} 𝒞] {I : Type vI} [Category.{wI} I]
  (D : I ⥤ 𝒞) (c : Cone D)

/-- For the identity functor every object over the vertex of a cone is a pullback of an object at
a stage, the stage being an arbitrary one. -/
private theorem descentObj_id [IsCofiltered I] :
    Deformation.Artin.DescentObj (𝟭 𝒞) D c := by
  intro x
  obtain ⟨i⟩ : Nonempty I := IsCofiltered.nonempty
  refine ⟨i, ⟨D.obj i, rfl⟩, eqToHom x.2 ≫ c.π.app i, ?_⟩
  exact IsHomLift.of_fac' (𝟭 𝒞) _ _ x.2 rfl (by simp)

/-- For the identity functor the identity of a stage object lies over the image of the identity
of its index. -/
private theorem isHomLift_id_map_id (i : I) (xi : (𝟭 𝒞).Fiber (D.obj i)) :
    (𝟭 𝒞).IsHomLift (D.map (𝟙 i)) (𝟙 xi.1) :=
  IsHomLift.of_fac' (𝟭 𝒞) _ _ xi.2 xi.2 (by simp)

/-- For the identity functor every vertical morphism between pullbacks of stage objects already
comes from the stage itself. -/
private theorem descentHom_id : Deformation.Artin.DescentHom (𝟭 𝒞) D c := by
  intro i xi yi x y δ ε hδ hε φ hφ
  have hψ : (𝟭 𝒞).IsHomLift (𝟙 (D.obj i)) (eqToHom (xi.2.trans yi.2.symm)) :=
    IsHomLift.of_fac' (𝟭 𝒞) _ _ xi.2 yi.2 (by simp)
  refine ⟨i, 𝟙 i, xi, yi, 𝟙 xi.1, 𝟙 yi.1, δ, eqToHom (xi.2.trans yi.2.symm),
    (isHomLift_id_map_id D i xi), (isHomLift_id_map_id D i yi), hδ, hψ, Category.comp_id δ, ?_⟩
  refine eq_of_isHomLift_id (c.π.app i) _ _ ?_ ?_
  · have := hδ
    have := hψ
    have h : (𝟭 𝒞).IsHomLift (c.π.app i ≫ 𝟙 (D.obj i))
        (δ ≫ eqToHom (xi.2.trans yi.2.symm) ≫ 𝟙 yi.1) := by
      simpa using
        (IsHomLift.comp_lift_id_right' (𝟭 𝒞) (c.π.app i) δ (D.obj i)
          (eqToHom (xi.2.trans yi.2.symm)))
    simpa using h
  · have := hφ
    have := hε
    exact IsHomLift.comp_lift_id_left' (𝟭 𝒞) c.pt φ (c.π.app i) ε

/-- For the identity functor two vertical morphisms of a stage which agree over the vertex of a
cone are equal. -/
private theorem descentEq_id : Deformation.Artin.DescentEq (𝟭 𝒞) D c := by
  intro i xi yi x δ hδ ψ ψ' hψ hψ' _
  refine ⟨i, 𝟙 i, xi, 𝟙 xi.1, isHomLift_id_map_id D i xi, ?_⟩
  rw [eq_of_isHomLift_id (𝟙 (D.obj i)) ψ ψ' hψ hψ']

end Identity

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))

/-- **The big fppf site of `S` is limit preserving.** Viewed as a category fibred in groupoids
over itself by the identity functor, its comparison from the colimit of the fibres over the
stages of a cofiltered inverse system of affine schemes to the fibre over the limit is an
equivalence. -/
theorem isLimitPreserving_terminalCFG :
    Deformation.Artin.IsLimitPreserving.{u, v, w, u + 1, u} B S hS (terminalCFG B S hS) := by
  intro I _ _ D c _
  have hgp : Functor.IsFiberedInGroupoids (𝟭 (BigFppfOver B S hS)) :=
    Functor.isFiberedInGroupoids_id
  have : Functor.IsFibered (𝟭 (BigFppfOver B S hS)) := hgp.isFibered
  exact
    ⟨Deformation.Artin.faithful_of_descentEq _ hgp _ _
        (descentEq_id (D ⋙ BigAffineFppf.inclusion B S hS)
          ((BigAffineFppf.inclusion B S hS).mapCone c)),
      Deformation.Artin.full_of_descentHom _ hgp _ _
        (descentHom_id (D ⋙ BigAffineFppf.inclusion B S hS)
          ((BigAffineFppf.inclusion B S hS).mapCone c)),
      Deformation.Artin.essSurj_of_descentObj _ hgp _ _
        (descentObj_id (D ⋙ BigAffineFppf.inclusion B S hS)
          ((BigAffineFppf.inclusion B S hS).mapCone c))⟩

/-- **The self-product of a limit preserving category fibred in groupoids is limit preserving.**
This is Stacks 07XM, part (2), read for the 2-fibre product of `𝒳` with itself over the big fppf
site of `S`, which is the product `𝒳 × 𝒳`. -/
theorem isLimitPreserving_product
    (h𝒳 : Deformation.Artin.IsLimitPreserving.{u, v, w, u + 1, u} B S hS 𝒳) :
    Deformation.Artin.IsLimitPreserving.{u, v, w, u + 1, u} B S hS
      (CatFiberedInGroupoids.product 𝒳 𝒳) :=
  isLimitPreserving_twoFibreProduct B S hS 𝒳 (terminalCFG B S hS) 𝒳
    (Bicategory.InducedBicategory.mkHom (toTerminalCFG B S hS 𝒳))
    (Bicategory.InducedBicategory.mkHom (toTerminalCFG B S hS 𝒳))
    h𝒳 (isLimitPreserving_terminalCFG B S hS) h𝒳

/-- **The structure morphism of the self-product of a limit preserving category fibred in
groupoids is limit preserving on objects.** Every object of `𝒳 × 𝒳` over an affine inverse limit
descends to a finite stage, which is the condition of Stacks 06CU for
`𝒳 × 𝒳 ⟶ (Sch/S)_{fppf}`.

This is Stacks 07XM, part (1), read for the 2-fibre product of `𝒳` with itself over the big fppf
site of `S`, with the structure morphism of `𝒳` limit preserving on objects by Stacks 07XN. -/
theorem isLimitPreservingOnObjects_toTerminalCFG_product
    (h𝒳 : Deformation.Artin.IsLimitPreserving.{u, v, w, u + 1, u} B S hS 𝒳) :
    BigFppfOver.IsLimitPreservingOnObjects.{u, v, w, u, u + 1} B S hS
      (CatFiberedInGroupoids.product 𝒳 𝒳) (terminalCFG B S hS)
      (Bicategory.InducedBicategory.mkHom
        (toTerminalCFG B S hS (CatFiberedInGroupoids.product 𝒳 𝒳))) :=
  isLimitPreservingOnObjects_toTerminalCFG_twoFibreProduct B S hS 𝒳 (terminalCFG B S hS) 𝒳
    (Bicategory.InducedBicategory.mkHom (toTerminalCFG B S hS 𝒳))
    (Bicategory.InducedBicategory.mkHom (toTerminalCFG B S hS 𝒳))
    (isLimitPreservingOnObjects_toTerminalCFG_of_isLimitPreserving B S hS 𝒳 h𝒳)
    (isLimitPreservingOnObjects_toTerminalCFG_of_isLimitPreserving B S hS 𝒳 h𝒳)
    (isLimitPreserving_terminalCFG B S hS)

end AlgebraicGeometry.Stack

end
