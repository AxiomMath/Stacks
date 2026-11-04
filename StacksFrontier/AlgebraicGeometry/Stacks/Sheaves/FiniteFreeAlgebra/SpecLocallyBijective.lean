module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.AffineRefinement
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.FiniteFreeAlgebra.SpecFibreFullyFaithful

/-!
# Clause (1) of Stacks 02ZN for the 1-morphism `Spec`

Let `S` be a scheme of a big fppf site and let `d` be a positive natural number. For two free
rank-`d` structures over an object `U` of the big fppf site over `S`, the map of morphism
presheaves of Stacks 042V attached to the 1-morphism `Spec` of Stacks 05YQ is locally injective
and locally surjective for the fppf topology on the site over `U`: it is bijective over every
object of that site whose underlying scheme is affine, and the affine objects are cofinal.

This is clause (1) of Stacks 02ZN for `Spec`, that is clause (a) of the proof of 05YQ; together
with `AlgebraicGeometry.FiniteFreeAlgebra.essImage_specFiniteCover`, clause (2), it is what
`AlgebraicGeometry.Stack.nonempty_isEquivalenceOver_extend_toQuotientStack` consumes.

## Main results

* `AlgebraicGeometry.FiniteFreeAlgebra.bijective_morPresheafMap_app`: over an object of the site
  over `U` whose underlying scheme is affine, the map of morphism presheaves is bijective.
* `AlgebraicGeometry.FiniteFreeAlgebra.isLocallyBijective_specFiniteCover`: **clause (1) of
  Stacks 02ZN for `Spec`.**

## Implementation notes

The component of `CategoryTheory.Functor.IsFibredOneMorphism.morPresheafMap` over an object `g` of
the site over `U` is, by `CategoryTheory.Functor.IsFibredOneMorphism.morPresheafMap_app`, the
functor induced by `Spec` on the fibres over the underlying object of `g` conjugated by the
comparison isomorphisms `CategoryTheory.Functor.IsFibredOneMorphism.mapPullbackFiberIso`;
conjugation by isomorphisms is `CategoryTheory.Iso.homCongr`, an equivalence, so bijectivity of
the component is exactly the affine statement
`AlgebraicGeometry.FiniteFreeAlgebra.bijective_fiberFunctorOfCompEq_map`.

Both clauses of local bijectivity are membership of a sieve on an object `g` of the site over `U`
— a sieve of equalities for the first and a sieve of liftings for the second — and both sieves
contain the open immersions of the affine opens of `g` lying over affine opens of `S`, which is a
covering family by `AlgebraicGeometry.BigFppfOver.mem_overTopology_of_openSubObj`. Over such an
open the component is bijective, the open being affine by
`AlgebraicGeometry.BigFppfOver.isAffine_affineSubordinateCoverSlice_obj`; for injectivity the
restriction of the two sections agree there because the component is injective there and, by
naturality, carries each restriction to the restriction of its image.

## References

* [Stacks Project, Tag 02ZN](https://stacks.math.columbia.edu/tag/02ZN)
* [Stacks Project, Tag 05YQ](https://stacks.math.columbia.edu/tag/05YQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CommRingCat

universe u

namespace AlgebraicGeometry.FiniteFreeAlgebra

attribute [local instance] FiniteFreeAlgebra.groupoid

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S} {d : ℕ} [NeZero d]

/-- **Over an object of the site over `U` whose underlying scheme is affine, the map of morphism
presheaves attached to `Spec` is bijective.** Its component there is the fibre functor of `Spec`
conjugated by the comparison isomorphisms of the chosen pullbacks, and conjugation by
isomorphisms is a bijection. -/
theorem bijective_morPresheafMap_app (U : BigFppfOver 𝒞 S hS)
    (a b : (CategoryTheory.presheafOfGroupoids (ffaSitePresheaf 𝒞 S hS d)).p.Fiber U)
    (g : (Over U)ᵒᵖ)
    [IsAffine ((BigFppfOver.toScheme 𝒞 S hS).obj g.unop.left)] :
    Function.Bijective
      (((isFibredOneMorphism_specFiniteCover 𝒞 S hS d).morPresheafMap a b).app g) := by
  set e := (isFibredOneMorphism_specFiniteCover 𝒞 S hS d).mapPullbackFiberIso a g.unop.hom
  set e' := (isFibredOneMorphism_specFiniteCover 𝒞 S hS d).mapPullbackFiberIso b g.unop.hom
  have he : ⇑(((isFibredOneMorphism_specFiniteCover 𝒞 S hS d).morPresheafMap a b).app g) =
      (e.symm.homCongr e'.symm) ∘ (CategoryTheory.Functor.fiberFunctorOfCompEq
        (isFibredOneMorphism_specFiniteCover 𝒞 S hS d).comp_eq g.unop.left).map := rfl
  rw [he]
  exact (e.symm.homCongr e'.symm).bijective.comp
    (bijective_fiberFunctorOfCompEq_map g.unop.left _ _)

/-- **Clause (1) of Stacks 02ZN for the 1-morphism `Spec` of Stacks 05YQ**, that is clause (a) of
the proof of 05YQ. For every object `U` of the big fppf site over `S` and all two objects `a` and
`b` of the fibre over `U` of the pointwise groupoid fibration of free rank-`d` structures, the map
of morphism presheaves `Mor(a, b) ⟶ Mor(Spec a, Spec b)` of Stacks 042V is locally injective and
locally surjective for the fppf topology on the site over `U`. -/
theorem isLocallyBijective_specFiniteCover (U : BigFppfOver 𝒞 S hS)
    (a b : (CategoryTheory.presheafOfGroupoids (ffaSitePresheaf 𝒞 S hS d)).p.Fiber U) :
    CategoryTheory.Presheaf.IsLocallyInjective ((BigFppfOver.topology 𝒞 S hS).over U)
        ((isFibredOneMorphism_specFiniteCover 𝒞 S hS d).morPresheafMap a b) ∧
      CategoryTheory.Presheaf.IsLocallySurjective ((BigFppfOver.topology 𝒞 S hS).over U)
        ((isFibredOneMorphism_specFiniteCover 𝒞 S hS d).morPresheafMap a b) := by
  refine ⟨⟨?_⟩, ⟨?_⟩⟩
  · intro g s t hst
    refine BigFppfOver.mem_overTopology_of_openSubObj 𝒞 S hS g.unop _ fun i => ?_
    have : IsAffine ((BigFppfOver.toScheme 𝒞 S hS).obj
        (Over.mk (BigFppfOver.openSubHom 𝒞 S hS g.unop.left i.down.1.1 ≫ g.unop.hom)).left) :=
      BigFppfOver.isAffine_affineSubordinateCoverSlice_obj 𝒞 S hS g.unop i
    refine (bijective_morPresheafMap_app U a b (Opposite.op
      (Over.mk (BigFppfOver.openSubHom 𝒞 S hS g.unop.left i.down.1.1 ≫ g.unop.hom)))).1 ?_
    rw [NatTrans.naturality_apply, NatTrans.naturality_apply, hst]
  · intro g s
    refine BigFppfOver.mem_overTopology_of_openSubObj 𝒞 S hS g _ fun i => ?_
    have := BigFppfOver.isAffine_affineSubordinateCoverSlice_obj 𝒞 S hS g i
    exact (bijective_morPresheafMap_app U a b (Opposite.op
      ((BigFppfOver.affineSubordinateCoverSlice 𝒞 S hS g).X i))).2 _

end AlgebraicGeometry.FiniteFreeAlgebra

end
