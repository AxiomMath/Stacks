module

public import StacksFrontier.AlgebraicGeometry.Stacks.FormallySmoothOnObjectsLifting

/-!
# Formal smoothness on objects is invariant under 2-isomorphism

A 1-morphism of categories fibred in groupoids over the big fppf site of `S` is formally smooth
on objects (**Stacks 06D0**) exactly when every 1-morphism 2-isomorphic to it is: the lifting
problem of `AlgebraicGeometry.Stack.HasFirstOrderObjectLifts` is transported by composing its
datum with the component of the 2-isomorphism at the source object and its solution with the
component at the lifted object, and the two components cancel because every component of a
2-isomorphism is invertible.

## Main results

* `AlgebraicGeometry.Stack.hasFirstOrderObjectLifts_of_iso` and
  `AlgebraicGeometry.Stack.isFormallySmoothOnObjects_of_iso`: the transport.

## Implementation notes

The cancellation of the two components is read off the two identities of a 2-isomorphism by
`AlgebraicGeometry.Stack.app_hom_comp_app_inv` and
`AlgebraicGeometry.Stack.app_inv_comp_app_hom`: a 2-morphism of the 2-category of categories
fibred in groupoids is a morphism of the underlying functors over `S` (clause (3) of
**Stacks 02XS**), composed componentwise, so the two identities give the two componentwise ones.

Every component of a 2-morphism lies over an identity of the site, so the composites formed here
lie over the morphism of the site they are required to, by
`CategoryTheory.IsHomLift.comp_lift_id_left'` and
`CategoryTheory.IsHomLift.comp_lift_id_right'`.

## References

* [Stacks Project, Tag 02XS](https://stacks.math.columbia.edu/tag/02XS)
* [Stacks Project, Tag 06D0](https://stacks.math.columbia.edu/tag/06D0)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory
open Stacks.Thickenings

namespace AlgebraicGeometry.Stack

universe u v w

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {𝒳 𝒴 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}

/-- The component at an object of the forward 2-morphism of a 2-isomorphism, followed by the
component of its inverse, is the identity. -/
lemma app_hom_comp_app_inv {p q : 𝒳 ⟶ 𝒴} (ε : p ≅ q) (x : 𝒳.val.obj) :
    ε.hom.hom.toNatTrans.app x ≫ ε.inv.hom.toNatTrans.app x =
      𝟙 ((CatFiberedInGroupoids.homFunctor p).obj x) := by
  have h := congrArg (fun t : p ⟶ p => t.hom.toNatTrans.app x) ε.hom_inv_id
  exact h

/-- The component at an object of the inverse 2-morphism of a 2-isomorphism, followed by the
component of the forward one, is the identity. -/
lemma app_inv_comp_app_hom {p q : 𝒳 ⟶ 𝒴} (ε : p ≅ q) (x : 𝒳.val.obj) :
    ε.inv.hom.toNatTrans.app x ≫ ε.hom.hom.toNatTrans.app x =
      𝟙 ((CatFiberedInGroupoids.homFunctor q).obj x) := by
  have h := congrArg (fun t : q ⟶ q => t.hom.toNatTrans.app x) ε.inv_hom_id
  exact h

/-- **The first-order lifting property of Stacks 06D0 is invariant under 2-isomorphism.** If
`p : 𝒳 ⟶ 𝒴` solves every first-order lifting problem and `q` is 2-isomorphic to `p`, then `q`
solves every first-order lifting problem.

The datum of a lifting problem for `q` becomes one for `p` by composing with the component of the
2-isomorphism at the given object of `𝒳`, and the vertical identification `p x' ⟶ y'` that `p`
returns becomes one for `q` by composing with the component at `x'`; the compatibility equation
follows from naturality of the inverse 2-morphism at the morphism `x ⟶ x'`. -/
theorem hasFirstOrderObjectLifts_of_iso {p q : 𝒳 ⟶ 𝒴} (ε : p ≅ q)
    (hp : HasFirstOrderObjectLifts B S hS p) : HasFirstOrderObjectLifts B S hS q := by
  intro U U' i hU hU' hi x y' a ha
  have hεx : 𝒴.val.p.IsHomLift (𝟙 (𝒳.val.p.obj x.1)) (ε.hom.hom.toNatTrans.app x.1) :=
    CatFiberedInGroupoids.isHomLift_app ε.hom x.1
  have ha' : 𝒴.val.p.IsHomLift i (ε.hom.hom.toNatTrans.app x.1 ≫ a) :=
    @IsHomLift.comp_lift_id_left' _ _ _ _ 𝒴.val.p _ _ _ (𝒳.val.p.obj x.1)
      (ε.hom.hom.toNatTrans.app x.1) hεx _ _ i a ha
  obtain ⟨x', b, c, hb, hc, hbc⟩ :=
    hp U U' i hU hU' hi x y' (ε.hom.hom.toNatTrans.app x.1 ≫ a) ha'
  have hεx' : 𝒴.val.p.IsHomLift (𝟙 (𝒳.val.p.obj x'.1)) (ε.inv.hom.toNatTrans.app x'.1) :=
    CatFiberedInGroupoids.isHomLift_app ε.inv x'.1
  refine ⟨x', b, ε.inv.hom.toNatTrans.app x'.1 ≫ c, hb, ?_, ?_⟩
  · exact @IsHomLift.comp_lift_id_left' _ _ _ _ 𝒴.val.p _ _ _ (𝒳.val.p.obj x'.1)
      (ε.inv.hom.toNatTrans.app x'.1) hεx' _ _ (𝟙 U') c hc
  · have hnat : (CatFiberedInGroupoids.homFunctor q).map b ≫
        ε.inv.hom.toNatTrans.app x'.1 =
          ε.inv.hom.toNatTrans.app x.1 ≫ (CatFiberedInGroupoids.homFunctor p).map b :=
      ε.inv.hom.toNatTrans.naturality b
    rw [← Category.assoc, hnat, Category.assoc, hbc, ← Category.assoc,
      app_inv_comp_app_hom B S hS ε x.1, Category.id_comp]

/-- **Stacks 06D0 is invariant under 2-isomorphism.** A 1-morphism of categories fibred in
groupoids over the big fppf site of `S` 2-isomorphic to one that is formally smooth on objects is
formally smooth on objects. -/
theorem isFormallySmoothOnObjects_of_iso {p q : 𝒳 ⟶ 𝒴} (ε : p ≅ q)
    (hp : IsFormallySmoothOnObjects B S hS 𝒳 𝒴 p) :
    IsFormallySmoothOnObjects B S hS 𝒳 𝒴 q :=
  isFormallySmoothOnObjects_of_exists_homLift B S hS q
    (hasFirstOrderObjectLifts_of_iso B S hS ε
      (exists_homLift_of_isFormallySmoothOnObjects B S hS p hp))

end AlgebraicGeometry.Stack

end
