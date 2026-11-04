module

public import StacksFrontier.AlgebraicGeometry.Stacks.IsoClassPresheafUniverseModel
public import StacksFrontier.AlgebraicGeometry.Stacks.LocalEssentialSurjectivity

/-!
# Smallness of the fibres of the 2-fibre product of two scheme-valued points

Let `x : 𝒯₁ ⟶ 𝒳` and `y : 𝒯₂ ⟶ 𝒳` be 1-morphisms of categories fibred in groupoids over the big
fppf site of `S`. If the fibres of `𝒯₁` and `𝒯₂` are small and `𝒳` is locally small, then the
fibres of the 2-fibre product `𝒯₁ ×_𝒳 𝒯₂`, and its presheaf of isomorphism classes, are small.
For two scheme-valued points of `𝒳` no hypothesis remains.

## Main results

* `CategoryTheory.small_skeleton_of_small`: the skeleton of a small category is small.
* `AlgebraicGeometry.Stack.small_fiber_twoFibreProduct`: the fibres of a 2-fibre product are
  small when the fibres of the two sources are and the target is locally small.
* `AlgebraicGeometry.Stack.small_isoClassPresheaf_twoFibreProduct`: the same, for the presheaf of
  isomorphism classes.
* `AlgebraicGeometry.Stack.small_isoClassPresheaf_twoFibreProduct_schemePoints`: the instance of
  the previous result at two scheme-valued points, with no hypotheses left.

## References

* [Stacks Project, Tag 02ZX](https://stacks.math.columbia.edu/tag/02ZX)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
-/

@[expose] public section

open CategoryTheory Opposite

namespace CategoryTheory

universe w v u

/-- The skeleton of a small category is small. -/
public theorem small_skeleton_of_small (C : Type u) [Category.{v} C] [Small.{w} C] :
    Small.{w} (Skeleton C) :=
  small_of_surjective (f := toSkeleton (C := C)) Quotient.mk_surjective

end CategoryTheory

namespace AlgebraicGeometry.Stack

universe s u v w v₁ v₂ w₁ w₂

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section General

variable {𝒳 : CatFiberedInGroupoids.{u, v, u + 1, w} (BigFppfOver B S hS)}
  {𝒯₁ : CatFiberedInGroupoids.{u, v₁, u + 1, w₁} (BigFppfOver B S hS)}
  {𝒯₂ : CatFiberedInGroupoids.{u, v₂, u + 1, w₂} (BigFppfOver B S hS)}

/-- The fibres of the 2-fibre product of two 1-morphisms into `𝒳` are small as soon as the fibres
of the two sources are small and the morphisms of `𝒳` are. -/
public theorem small_fiber_twoFibreProduct
    (x : 𝒯₁.val ⥤ᵇ 𝒳.val) (y : 𝒯₂.val ⥤ᵇ 𝒳.val) (V : BigFppfOver B S hS)
    (h𝒳 : LocallySmall.{s} 𝒳.val.obj)
    (h₁ : Small.{s} (𝒯₁.val.p.Fiber V)) (h₂ : Small.{s} (𝒯₂.val.p.Fiber V)) :
    Small.{s} ((twoFibreProduct B S hS 𝒳 𝒯₁ 𝒯₂ x y).val.p.Fiber V) := by
  have := h𝒳
  have := h₁
  have := h₂
  refine small_of_injective
    (β := Σ ab : 𝒯₁.val.p.Fiber V × 𝒯₂.val.p.Fiber V,
      (x.toFunctor.obj ab.1.1 ⟶ y.toFunctor.obj ab.2.1))
    (f := fun P => ⟨(⟨P.1.x, P.1.hx.trans P.2⟩, ⟨P.1.y, P.1.hy.trans P.2⟩), P.1.iso.hom⟩) ?_
  rintro ⟨⟨bP, xP, yP, hxP, hyP, isoP, vP⟩, hP⟩ ⟨⟨bQ, xQ, yQ, hxQ, hyQ, isoQ, vQ⟩, hQ⟩ h
  obtain ⟨hab, hiso⟩ := Sigma.mk.inj_iff.1 h
  have hbP : bP = V := hP
  have hbQ : bQ = V := hQ
  have hx : xP = xQ := congrArg (fun t => t.1.1) hab
  have hy : yP = yQ := congrArg (fun t => t.2.1) hab
  subst hbP hbQ hx hy
  obtain rfl : isoP = isoQ := Iso.ext (eq_of_heq hiso)
  rfl

/-- The presheaf of isomorphism classes of the 2-fibre product is small under the hypotheses of
`AlgebraicGeometry.Stack.small_fiber_twoFibreProduct`. -/
public theorem small_isoClassPresheaf_twoFibreProduct
    (x : 𝒯₁.val ⥤ᵇ 𝒳.val) (y : 𝒯₂.val ⥤ᵇ 𝒳.val)
    [(twoFibreProduct B S hS 𝒳 𝒯₁ 𝒯₂ x y).val.p.IsFibered]
    (h𝒳 : LocallySmall.{s} 𝒳.val.obj)
    (h₁ : ∀ V : BigFppfOver B S hS, Small.{s} (𝒯₁.val.p.Fiber V))
    (h₂ : ∀ V : BigFppfOver B S hS, Small.{s} (𝒯₂.val.p.Fiber V)) :
    CategoryTheory.FunctorToTypes.Small.{s}
      (twoFibreProduct B S hS 𝒳 𝒯₁ 𝒯₂ x y).val.p.isoClassPresheaf := by
  intro V
  have := small_fiber_twoFibreProduct B S hS x y V.unop h𝒳 (h₁ V.unop) (h₂ V.unop)
  exact small_skeleton_of_small _

end General

section SchemePoints

variable {𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}

/-- The presheaf of isomorphism classes of the 2-fibre product of two scheme-valued points of `𝒳`
is `u`-small. -/
public theorem small_isoClassPresheaf_twoFibreProduct_schemePoints
    (U V : BigFppfOver B S hS)
    (x : (schemeFibredCategory B S hS U).val ⥤ᵇ 𝒳.val)
    (y : (schemeFibredCategory B S hS V).val ⥤ᵇ 𝒳.val)
    [(twoFibreProduct B S hS 𝒳
      (schemeFibredCategory B S hS U) (schemeFibredCategory B S hS V) x y).val.p.IsFibered] :
    CategoryTheory.FunctorToTypes.Small.{u}
      (CategoryTheory.Functor.isoClassPresheaf
        (twoFibreProduct B S hS 𝒳
          (schemeFibredCategory B S hS U) (schemeFibredCategory B S hS V) x y).val.p) :=
  small_isoClassPresheaf_twoFibreProduct B S hS x y inferInstance
    (small_fiber_schemeFibredCategory B S hS U) (small_fiber_schemeFibredCategory B S hS V)

end SchemePoints

end AlgebraicGeometry.Stack

end
