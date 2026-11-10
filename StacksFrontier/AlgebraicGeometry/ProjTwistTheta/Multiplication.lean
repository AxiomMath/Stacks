module

public import StacksFrontier.AlgebraicGeometry.ProjTwistTheta.DegreeSection
public import StacksFrontier.AlgebraicGeometry.PullbackTensorIso.Invertible
public import StacksFrontier.AlgebraicGeometry.TwistTensor.Basic

/-!
# The pulled-back multiplication on twists, and multiplicativity of the comparison maps

Tag 01MY asks that the comparison maps `theta n` on the twists be compatible with the
multiplication maps `O(n) tensor O(m) -> O(n+m)`. Stating that needs the comparison between
the pullback of a tensor product of module sheaves and the tensor product of the pullbacks,
Tag 01CD, and it is now available unconditionally as
`Stacks.PullbackTensorIso.pullbackTensorIso`. This file builds the pulled-back multiplication
map that the statement of Tag 01MY is phrased with, records the uniqueness principle for morphisms
out of a tensor product of sheaves of modules, and proves the mathematical content of the
compatibility: the comparison on sections is multiplicative.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjTwistTheta.pullbackTwistMultiplication`: for a morphism of
  schemes `f : X -> Proj S` and integers `n`, `m`, the multiplication
  `f^* O(n) tensor f^* O(m) -> f^* O(n+m)` obtained from the Tag 01CD comparison and the
  pullback of the multiplication map of Tag 01MU. This is Tag 01MY's
  `pullbackTwistMultiplication`, which no earlier round could write down.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistTheta.tensorSheaf_hom_ext`: two morphisms out of a tensor
  product of sheaves of modules on a ringed space that agree on the images of the pure tensors
  of sections are equal.
* `Stacks.AlgebraicGeometry.ProjTwistTheta.twistPushforwardMap_mul_val`: **the comparison on
  sections is multiplicative.** The adjoint form of `theta (n+m)`, applied to the product of two
  honest sections of `O(n)` and `O(m)`, has at every point the product of the values of the
  adjoint forms of `theta n` and `theta m` at that point.

## Why `pullbackTwistMultiplication` can now be written

Four identifications were checked, and all four hold by `rfl`, so no bridge is needed between
the ringed-space vocabulary in which Tag 01CD is proved and the scheme vocabulary in which the
Proj statements are stated: the structure sheaf of a scheme read as a sheaf of rings is the
structure
sheaf of its underlying ringed space read the same way; the morphism of sheaves of rings that
`CategoryTheory.SheafOfModules.pushforward` consumes is the same on both sides; hence
`AlgebraicGeometry.Scheme.Modules.pullback` of a morphism of schemes *is*
`Stacks.RingedSpace.pullbackFunctor` of the underlying morphism of ringed spaces; and the two
tensor products of sheaves of modules agree
(`Stacks.PullbackTensorIso.tensorSheaf_eq_tensorSheaf_obj`). The first three are verified by the
elaboration of `pullbackTwistMultiplication` itself, whose type is written in the scheme
vocabulary while its body is the ringed-space comparison.

## The route to multiplicativity

The adjoint form of the comparison has a pointwise formula
(`Stacks.AlgebraicGeometry.ProjTwistCompare.twistPushforwardMap_app_val`): the value at a point
of the domain of definition is the fibre comparison, a ring homomorphism between homogeneous
localizations, applied to the value of the argument at the image point. The multiplication map
on twists has a pointwise formula too
(`Stacks.AlgebraicGeometry.TwistTensor.twistMultiplicationMap_tmul`): on the image of a pure
tensor of honest sections its value is the product of the two values. So multiplicativity of
the comparison on sections is multiplicativity of the fibre comparison, which is `map_mul`.

## Implementation notes

The uniqueness principle is the sheafification adjunction with
`CategoryTheory.Adjunction.homEquiv_unit` applied as a *term* on each side rather than by
`rw`: after `refine ... .injective ?_` the goal mentions the tensor product through its own
definition, and a rewrite fails its motive check because the category instance on the
sheafification is reached by a different route than the one on the tensor product.

## What is not done

The compatibility assertion of Tag 01MY itself is **not** proved. With
`pullbackTwistMultiplication` available the assertion is now stateable, which it was not
before, and `twistPushforwardMap_mul_val` is its content on sections; what is missing is
transport, and it is exactly five steps:

1. Turn the assertion, whose source is a tensor product of *pullbacks*, into one whose source
   is the pullback of a tensor product, by composing with the Tag 01CD comparison, which is
   invertible.
2. Transpose across the pullback--pushforward adjunction, so that the source becomes a tensor
   product of twisting sheaves, whose sections are concrete; then `tensorSheaf_hom_ext`
   reduces the assertion to pure tensors of honest sections.
3. The forward Tag 01CD comparison on a pure tensor, which is
   `Stacks.RingedSpace.comparisonNatTrans_homEquiv_unit_tmul`, read in the inverse direction.
4. The identification of
   `AlgebraicGeometry.Scheme.Modules.restrictFunctorIsoPullback` applied to a section with the
   unit of the pullback adjunction at the image open; this is
   `Stacks.AlgebraicGeometry.ProjTwistTheta.restrictUnit_comp_map_restrictFunctorIsoPullback`
   of the companion file, read at the open `ι ''ᵁ V`, and it needs the transport along
   `AlgebraicGeometry.Scheme.Hom.preimage_image_eq`, which is a propositional equality of
   opens and not a definitional one.
5. Naturality of the pullback unit in the module argument, to move the multiplication map
   through it.

Nothing here is stated about the unit law, about uniqueness of the family of comparison maps,
or about the comparison being an isomorphism.

## References

* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
* [Stacks Project, Tag 01MU](https://stacks.math.columbia.edu/tag/01MU)
* [Stacks Project, Tag 01CB](https://stacks.math.columbia.edu/tag/01CB)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry HomogeneousLocalization TopologicalSpace CategoryTheory Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjShared Stacks.AlgebraicGeometry.ProjTwistChain
open Stacks.AlgebraicGeometry.ProjTwistCompare Stacks.AlgebraicGeometry.ProjInvertibleLocus
open scoped TensorProduct

namespace Stacks.AlgebraicGeometry.ProjTwistTheta

universe u w w'

attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj
  TopCat.Presheaf.IsSheaf
attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top

/-! ### Morphisms out of a tensor product of sheaves of modules -/

/-- Two morphisms out of the tensor product `F ⊗ G` of sheaves of modules on a ringed space
which agree on the image of every pure tensor of sections are equal.

The tensor product is the sheafification of the objectwise tensor product, and
`Stacks.AlgebraicGeometry.ProjTwistTheta.tensorSheaf_hom_ext` is the sheafification adjunction:
the adjoint transpose is injective, and two morphisms out of the objectwise tensor product
agree as soon as they agree on pure tensors. -/
public theorem tensorSheaf_hom_ext {X : RingedSpace.{u, u}}
    {F G N : SheafOfModules.{u} (structureSheafRing X)}
    (α β : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨((X)).presheaf, ((X)).IsSheaf⟩).obj (F)).obj (G)) ⟶ N)
    (h : ∀ (U : (Opens X.carrier)ᵒᵖ) (x : F.val.obj U) (y : G.val.obj U),
      (α.val.app U).hom
        (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X F G U (x ⊗ₜ y)) =
        (β.val.app U).hom
          (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection X F G U (x ⊗ₜ y))) :
    α = β := by
  refine PresheafOfModules.sheafification_hom_ext
    (PresheafOfModules.tensorObj_hom_ext fun U x y => ?_)
  exact h U x y

/-! ### The pulled-back multiplication on twists -/

section Pullback

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- **Tag 01MY's pulled-back multiplication on twists.** For a morphism of schemes
`f : X ⟶ Proj S`, the multiplication `f^* O(n) ⊗ f^* O(m) ⟶ f^* O(n+m)`: the inverse of the
Tag 01CD comparison between the pullback of a tensor product and the tensor product of the
pullbacks, followed by the pullback of the multiplication map of Tag 01MU.

The comparison is invertible unconditionally by
`Stacks.PullbackTensorIso.pullbackTensorIso`, which is what makes this definition possible. -/
public def pullbackTwistMultiplication
    {X : Scheme.{u}} (f : X ⟶ AlgebraicGeometry.Proj 𝒮) (n m : ℤ) :
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj
          (((Scheme.Modules.pullback f).obj (twistingSheaf 𝒮 n)))).obj
        (((Scheme.Modules.pullback f).obj (twistingSheaf 𝒮 m)))) ⟶
      (Scheme.Modules.pullback f).obj (twistingSheaf 𝒮 (n + m)) :=
  (Stacks.PullbackTensorIso.pullbackTensorIso f.toLRSHom.toShHom).inv.app
      (twistingSheaf 𝒮 n, twistingSheaf 𝒮 m) ≫
    (Scheme.Modules.pullback f).map (twistMultiplicationMap 𝒮 n m)

/-- The forward direction of the Tag 01CD comparison is the one the pulled-back multiplication
inverts: `pullbackTwistMultiplication` composed on the left with the comparison is the pullback
of the multiplication map. -/
public theorem comparison_comp_pullbackTwistMultiplication
    {X : Scheme.{u}} (f : X ⟶ AlgebraicGeometry.Proj 𝒮) (n m : ℤ) :
    (Stacks.PullbackTensorIso.pullbackTensorIso f.toLRSHom.toShHom).hom.app
          (twistingSheaf 𝒮 n, twistingSheaf 𝒮 m) ≫
        pullbackTwistMultiplication 𝒮 f n m =
      (Scheme.Modules.pullback f).map (twistMultiplicationMap 𝒮 n m) :=
  Eq.trans (Category.assoc _ _ _).symm
    (Eq.trans
      (congrArg (fun k => k ≫ (Scheme.Modules.pullback f).map (twistMultiplicationMap 𝒮 n m))
        (Iso.hom_inv_id_app
          (Stacks.PullbackTensorIso.pullbackTensorIso f.toLRSHom.toShHom)
          (twistingSheaf 𝒮 n, twistingSheaf 𝒮 m)))
      (Category.id_comp _))

end Pullback

/-! ### Multiplicativity of the comparison on sections -/

section Compare

variable {A B : Type u} {σ : Type w} {τ : Type w'}
  [CommRing A] [CommRing B] [SetLike σ A] [AddSubgroupClass σ A]
  [SetLike τ B] [AddSubgroupClass τ B]
  (𝒜 : ℕ → σ) (ℬ : ℕ → τ) [GradedRing 𝒜] [GradedRing ℬ]

/-- **The comparison on sections of the twists is multiplicative.** For honest sections `s` of
`O(n)` and `t` of `O(m)` over an open `U` of `Proj A`, the adjoint form of the comparison on the
`(n+m)`-th twist, applied to the product section, has at every point of the image of
`mapHom ⁻¹ᵁ U` the product of the values there of the adjoint forms of the comparisons on the
`n`-th and the `m`-th twists.

This is the content of Tag 01MY's compatibility of the comparison maps with the multiplication
maps: the fibre comparison is a ring homomorphism, and both the multiplication map and the
comparison are given pointwise. -/
public theorem twistPushforwardMap_mul_val (ψ : 𝒜 →+*ᵍ ℬ) (n m : ℤ)
    (U : (AlgebraicGeometry.Proj 𝒜).Opens)
    (s : (twistingSheaf 𝒜 n).val.obj (.op U)) (t : (twistingSheaf 𝒜 m).val.obj (.op U))
    (z : ↑((mapDomain 𝒜 ℬ ψ).ι ''ᵁ (mapHom 𝒜 ℬ ψ ⁻¹ᵁ U))) :
    (((twistPushforwardMap 𝒜 ℬ ψ (n + m)).val.app (.op U)).hom'
        (((twistMultiplicationMap 𝒜 n m).val.app (.op U)).hom
          (Stacks.SheafOfModules.TensorStalkRingedSpace.toTensorSheafSection
            (AlgebraicGeometry.Proj 𝒜).toRingedSpace
            (twistingSheaf 𝒜 n) (twistingSheaf 𝒜 m) (.op U) (s ⊗ₜ t)))).1 z =
      (((twistPushforwardMap 𝒜 ℬ ψ n).val.app (.op U)).hom' s).1 z *
        (((twistPushforwardMap 𝒜 ℬ ψ m).val.app (.op U)).hom' t).1 z := by
  refine Eq.trans (twistPushforwardMap_app_val 𝒜 ℬ ψ (n + m) (.op U) _ z) ?_
  refine Eq.trans (congrArg (twistFibreMap 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z))
    (Stacks.AlgebraicGeometry.TwistTensor.twistMultiplicationMap_tmul 𝒜 n m U s t
      ⟨basePoint 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z), liftPt_mem 𝒜 ℬ ψ z⟩)) ?_
  refine Eq.trans (map_mul (twistFibreMap 𝒜 ℬ ψ (liftPt 𝒜 ℬ ψ z)) _ _) ?_
  exact congrArg₂ (· * ·)
    (twistPushforwardMap_app_val 𝒜 ℬ ψ n (.op U) s z).symm
    (twistPushforwardMap_app_val 𝒜 ℬ ψ m (.op U) t z).symm

end Compare

end Stacks.AlgebraicGeometry.ProjTwistTheta

end
