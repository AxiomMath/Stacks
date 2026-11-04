module

public import StacksFrontier.AlgebraicGeometry.Stacks.FiniteHilbert.HilbertCoverDiagonal
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.FiberIso

/-!
# The chosen pullback in `ℋ_d` is the fibre product of the cover

A descent datum relative to a sieve, `CategoryTheory.Functor.SieveDescentDatum`, is a family of
objects of the fibres together with gluing isomorphisms between their *chosen* pullbacks, and its
effectivity is an equation between morphisms out of those chosen pullbacks.  The chosen pullback
of `CategoryTheory.Functor.IsPreFibered` is produced by a choice, so for the category `ℋ_d` of
degree-`d` finite locally free covers nothing is known about it beyond its defining universal
property.  This file identifies it: the chosen pullback of a cover `Z ⟶ U` along `ε : V ⟶ U` is
canonically isomorphic, in the fibre over `V`, to the fibre product `Z ×_U V ⟶ V`, which is
`AlgebraicGeometry.Stack.finiteCoverPointObj`.

The comparison is the canonical one between two cartesian lifts,
`CategoryTheory.Functor.fiberIsoOfCartesian`.  What makes it available is that in `ℋ_d` *every*
morphism is cartesian over its base component: `ℋ_d` is fibred in groupoids, by
`AlgebraicGeometry.Stack.isFiberedInGroupoids_finiteCoverProjection`, and in a category fibred in
groupoids every lift of a base morphism is strongly cartesian.

## Main results

* `AlgebraicGeometry.Stack.isCartesian_of_isHomLift`: a morphism of `ℋ_d` lying over a morphism
  of the big fppf site is cartesian over it.
* `AlgebraicGeometry.Stack.fiberPointObj`: the fibre product `Z ×_U V ⟶ V`, read as an object of
  the fibre of `ℋ_d` over `V`.
* `AlgebraicGeometry.Stack.isHomLift_fiberPointHom`: the projection of
  `AlgebraicGeometry.Stack.fiberPointHom` lies over `ε`.
* `AlgebraicGeometry.Stack.pullbackFiberIsoPointObj`: **the chosen pullback along `ε` of an
  object of a fibre of `ℋ_d` is the fibre product of its cover along `ε`.**
* `AlgebraicGeometry.Stack.fiberInclusion_pullbackFiberIsoPointObj_hom_comp` and
  `AlgebraicGeometry.Stack.fiberInclusion_pullbackFiberIsoPointObj_inv_comp`: the two
  factorisations the comparison satisfies, which are what rewrite an equation stated at the chosen
  pullback into one stated at the fibre product.

## Implementation notes

No tag attribute sits on anything here.  Identifying a chosen pullback with a fibre product is
bookkeeping internal to the formalisation of Stacks 026B; the source has no corresponding
statement, because it works with the fibre products directly.

The comparison is an `abbrev`, so the two factorisations it satisfies are the `simp` lemmas
`CategoryTheory.Functor.fiberIsoOfCartesian_hom_fac` and
`CategoryTheory.Functor.fiberIsoOfCartesian_inv_fac` read at it.  They are recorded below in the
spelling a rewrite needs, and each is proved by `simp` rather than by the corresponding term:
elaborating the term against this statement exhausts the heartbeat budget, while `simp`, which
rewrites rather than unifies, closes it immediately.

The object of the fibre is written `⟨finiteCoverPointObj …, rfl⟩`: the projection
`AlgebraicGeometry.Stack.finiteCoverProjection` reads off the base object of a cover, and the base
object of `finiteCoverPointObj c hc (Over.mk ε)` is the source of `ε` definitionally, so the
membership proof is `rfl` and no `eqToHom` enters on that side.  On the other side the cover of
`x` is a cover of `x.1.U`, which is only *equal* to `U`, and that is where
`AlgebraicGeometry.Stack.fiberCoverHom` puts its `eqToHom`.

## References

* [Stacks Project, Tag 026B](https://stacks.math.columbia.edu/tag/026B)
* [Stacks Project, Tag 003V](https://stacks.math.columbia.edu/tag/003V)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Stack

attribute [local implicit_reducible] finiteCoverPointObj finiteCoverProjection
  CategoryTheory.Functor.Fiber CategoryTheory.Functor.Fiber.fiberInclusion

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {d : ℕ}

/-- **The category of degree-`d` finite locally free covers is a fibred category over the big
fppf site of `S`.**  This is the `IsFibered` half of
`AlgebraicGeometry.Stack.isFiberedInGroupoids_finiteCoverProjection`, registered as an instance so
that the chosen pullbacks of `ℋ_d` may be written without carrying the instance by hand. -/
instance isFibered_finiteCoverProjection :
    (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).IsFibered :=
  (isFiberedInGroupoids_finiteCoverProjection
    (B := B) (S := S) (hS := hS) (d := d)).isFibered

/-- **Every morphism of `ℋ_d` is cartesian over its base component.** The category of degree-`d`
finite locally free covers is fibred in groupoids, and in a category fibred in groupoids every
lift of a morphism of the base is strongly cartesian over it, hence cartesian. -/
theorem isCartesian_of_isHomLift {V U : BigFppfOver B S hS} (ε : V ⟶ U)
    {P Q : FiniteCover B S hS d} (φ : P ⟶ Q)
    (hφ : (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).IsHomLift ε φ) :
    (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).IsCartesian ε φ :=
  have := hφ
  have := (isFiberedInGroupoids_finiteCoverProjection
    (B := B) (S := S) (hS := hS) (d := d)).isStronglyCartesian_homLift ε φ
  inferInstance

/-- The base change along `ε : V ⟶ U` of the cover underlying an object of the fibre of `ℋ_d`
over `U`, read as an object of the fibre over `V`. -/
abbrev fiberPointObj {V U : BigFppfOver B S hS}
    (x : (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).Fiber U) (ε : V ⟶ U) :
    (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).Fiber V :=
  ⟨finiteCoverPointObj (fiberCoverHom x) (isFiniteLocallyFreeOfRank_fiberCoverHom x)
    (Over.mk ε), rfl⟩

/-- The morphism of `ℋ_d` out of the base change of `x` along `ε` lies over `ε`. -/
theorem isHomLift_fiberPointHom {V U : BigFppfOver B S hS}
    (x : (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).Fiber U) (ε : V ⟶ U) :
    (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).IsHomLift ε
      (fiberPointHom x (Over.mk ε)) :=
  CategoryTheory.IsHomLift.of_fac' _ ε (fiberPointHom x (Over.mk ε)) rfl x.2 (by
    show (Over.mk ε).hom ≫ eqToHom x.2.symm = eqToHom rfl ≫ ε ≫ eqToHom x.2.symm
    simp)

/-- The morphism of `ℋ_d` out of the base change of `x` along `ε` is cartesian over `ε`. -/
theorem isCartesian_fiberPointHom {V U : BigFppfOver B S hS}
    (x : (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).Fiber U) (ε : V ⟶ U) :
    (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).IsCartesian ε
      (fiberPointHom x (Over.mk ε)) :=
  isCartesian_of_isHomLift ε _ (isHomLift_fiberPointHom x ε)

/-- **The chosen pullback along `ε` of an object of a fibre of `ℋ_d` is the fibre product of its
cover along `ε`.** Both carry a cartesian morphism over `ε` into `x`, the first by the defining
property of a choice of pullbacks and the second by
`AlgebraicGeometry.Stack.isCartesian_fiberPointHom`, so they are canonically isomorphic in the
fibre over the source of `ε`.

It is an `abbrev` so that the two factorisations of
`CategoryTheory.Functor.fiberIsoOfCartesian` — which are `simp` lemmas — apply to it without a
further pair of restatements. -/
abbrev pullbackFiberIsoPointObj {V U : BigFppfOver B S hS}
    (x : (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).Fiber U) (ε : V ⟶ U) :
    Functor.pullbackFiber (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)) x ε ≅
      fiberPointObj x ε :=
  Functor.fiberIsoOfCartesian ε (Functor.IsPreFibered.pullbackMap x.2 ε)
    (fiberPointHom x (Over.mk ε))
    (Functor.IsPreFibered.pullbackMap.IsCartesian x.2 ε) (isCartesian_fiberPointHom x ε)

/-- **The chosen cartesian lift of `ε` at `x` is the projection of the fibre product of the cover
of `x` along `ε`, read through the comparison.** This is the equation that rewrites the chosen
pullbacks appearing in `CategoryTheory.Functor.SieveDescentDatum.IsEffective` into the fibre
products of covers. -/
theorem fiberInclusion_pullbackFiberIsoPointObj_hom_comp {V U : BigFppfOver B S hS}
    (x : (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).Fiber U) (ε : V ⟶ U) :
    Functor.Fiber.fiberInclusion.map (pullbackFiberIsoPointObj x ε).hom ≫
        fiberPointHom x (Over.mk ε) =
      Functor.IsPreFibered.pullbackMap x.2 ε := by
  simp

/-- **The projection of the fibre product of the cover of `x` along `ε` is the chosen cartesian
lift of `ε` at `x`, read through the comparison.** This is
`AlgebraicGeometry.Stack.fiberInclusion_pullbackFiberIsoPointObj_hom_comp` in the inverse
direction. -/
@[reassoc]
theorem fiberInclusion_pullbackFiberIsoPointObj_inv_comp {V U : BigFppfOver B S hS}
    (x : (finiteCoverProjection (B := B) (S := S) (hS := hS) (d := d)).Fiber U) (ε : V ⟶ U) :
    Functor.Fiber.fiberInclusion.map (pullbackFiberIsoPointObj x ε).inv ≫
        Functor.IsPreFibered.pullbackMap x.2 ε =
      fiberPointHom x (Over.mk ε) := by
  simp

end AlgebraicGeometry.Stack

end
