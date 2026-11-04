module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedStackUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreObjectTwoYoneda
public import StacksFrontier.AlgebraicGeometry.Stacks.PresheafFibredCategory
public import StacksFrontier.CategoryTheory.FiberedCategory.SliceAsElements

/-!
# The 1-morphism to `𝒫olarized` named by a polarized family

The proof of Stacks 0E96 uses the 1-morphism `H → 𝒫olarized` that the universal family of the
Hilbert space `H` determines (Stacks 0D3W with Stacks 0E94). Its construction has two halves: the
family over `H`, and the passage from a family over an object of the site to a 1-morphism out of
the represented category. This file does the second half, for an arbitrary polarized family over
an arbitrary object `U₀` of the big fppf site of a terminal base scheme.

It is the 2-Yoneda lemma (Stacks 004B,
`CategoryTheory.Functor.twoYonedaEvaluation_isEquivalence`): the 1-morphism named by an object of
the fibre over `U₀` is `CategoryTheory.Functor.TwoYoneda.liftBased`, built from a chosen cartesian
lift of the family along each morphism of the site to `U₀`, and the source of that 1-morphism is
the slice `(Sch/U₀)_{fppf}`, which is the category of elements of the presheaf `U₀` represents
(`CategoryTheory.PresheafOfCategories.sliceElementsEquivalenceOver`). Composing the two gives a
1-morphism out of `AlgebraicGeometry.Stack.fibredCategory` of that presheaf, which is the shape a
chart of a stack takes (`AlgebraicGeometry.Stack.SpaceChart`).

## Main definitions

* `AlgebraicGeometry.polarizedClassifyingMap`: **the 1-morphism `𝒮_{U₀} → 𝒫olarized` named by a
  polarized family over `U₀`.**

## Main results

* `CategoryTheory.Functor.TwoYoneda.nonempty_hom_liftBased_obj`: the value of the 1-morphism named
  by an object `x` of a fibre, at an object `a` of the slice, maps to every object carrying a
  morphism to `x` over `a.hom` — because both are cartesian lifts of `x` along `a.hom`.
* `AlgebraicGeometry.polarizedClassifyingMap_obj`: its value at a point `(V, v)` of `U₀` is the
  chosen cartesian lift of the family along `v`.
* `AlgebraicGeometry.nonempty_hom_polarizedClassifyingMap_obj`: that value maps to every polarized
  family carrying a morphism to the given one over `v`.

## Implementation notes

The 1-morphism cannot be built by choosing base changes and checking functoriality on the nose: the
base change of a polarized family involves a chosen fibre product of schemes and a chosen module
pullback, so `(g ∘ f)^*` is only isomorphic to `f^* g^*`. The 2-Yoneda construction avoids this,
the action on a morphism of the slice being the *unique* vertical fill-in between two cartesian
lifts, whose uniqueness gives functoriality. So nothing here needs a strictly functorial base
change, in contrast with `AlgebraicGeometry.SpacesOverSpace.baseChangeFunctor` (Stacks 0E93),
whose families are presheaves and whose base change is a pointwise fibre product.

## References

* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
* [Stacks Project, Tag 0D3W](https://stacks.math.columbia.edu/tag/0D3W)
* [Stacks Project, Tag 0E93](https://stacks.math.columbia.edu/tag/0E93)
* [Stacks Project, Tag 0E94](https://stacks.math.columbia.edu/tag/0E94)
* [Stacks Project, Tag 0E96](https://stacks.math.columbia.edu/tag/0E96)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor.TwoYoneda

universe v₁ u₁ v₂ u₂

variable {C : Type u₁} [Category.{v₁} C] {𝒮 : Type u₂} [Category.{v₂} 𝒮]

/-- **The value of the 1-morphism named by a fibre object maps to every cartesian lift.** Let `p`
be fibred in groupoids, let `x` be an object of the fibre over `U` and let `a` be an object of the
slice over `U`. Any object `w` carrying a morphism `ψ : w ⟶ x` over `a.hom` is a cartesian lift of
`x` along `a.hom`, as is the chosen lift that the 1-morphism named by `x` takes at `a`; in a
category fibred in groupoids every lift is strongly cartesian
(`CategoryTheory.Functor.IsFiberedInGroupoids.isStronglyCartesian_homLift`), so the two are
isomorphic over the identity. -/
theorem nonempty_hom_liftBased_obj (p : 𝒮 ⥤ C) (hp : p.IsFiberedInGroupoids) (U : C)
    (x : p.Fiber U) (a : Over U) {w : 𝒮} (ψ : w ⟶ x.1) (hψ : p.IsHomLift a.hom ψ) :
    Nonempty ((liftBased p hp U x).obj a ⟶ w) := by
  have := hψ
  have := hp.isStronglyCartesian_homLift a.hom ψ
  have hrefl : a.hom = (Iso.refl a.left).hom ≫ a.hom := by simp
  exact ⟨(Functor.IsStronglyCartesian.domainIsoOfBaseIso p hrefl ψ (chosenLift p hp U x a).φ).hom⟩

end CategoryTheory.Functor.TwoYoneda

namespace AlgebraicGeometry

universe u

variable (B : BigFppfSite.{u}) {S : Scheme.{u}} (hS : B.Contains S)
  (hT : IsTerminal (B.obj hS)) (U₀ : BigFppfOver B S hS)

/-- **The 1-morphism `𝒮_{U₀} → 𝒫olarized` named by a polarized family over `U₀`.** For an object
`U₀` of the big fppf site of a terminal base scheme and a polarized family `x₀` whose base is the
underlying scheme of `U₀`, this is the 1-morphism of the 2-Yoneda lemma (Stacks 004B) from the
category of elements of the presheaf `U₀` represents to `𝒫olarized`: it sends a point `(V, v)` of
`U₀` to a chosen cartesian lift of `x₀` along `v`, that is to a base change of `x₀`.

It is the composite of the identification of the category of elements of the presheaf `U₀`
represents with the slice over `U₀`
(`CategoryTheory.PresheafOfCategories.sliceElementsEquivalenceOver`) with
`CategoryTheory.Functor.TwoYoneda.liftBased` at the family read as an object of the fibre
(`AlgebraicGeometry.polarizedFiberMk`). -/
def polarizedClassifyingMap (x₀ : PolarizedFamily B) (h : x₀.base = U₀.left) :
    (Stack.fibredCategory B S hS (yoneda.obj U₀)).val ⥤ᵇ
      (polarizedStackUnconditional B hS hT).val :=
  BasedFunctor.comp
    { toFunctor := (PresheafOfCategories.sliceElementsEquivalenceOver U₀).inv.functor
      w := (PresheafOfCategories.sliceElementsEquivalenceOver U₀).inv.w }
    (Functor.TwoYoneda.liftBased (polarizedSliceProjection B hS hT)
      (polarizedStackUnconditional B hS hT).isFiberedInGroupoids U₀
      (polarizedFiberMk B hS hT x₀ h))

/-- The value of `AlgebraicGeometry.polarizedClassifyingMap` at a point `(V, v)` of `U₀` is the
chosen cartesian lift of the family along `v`. -/
theorem polarizedClassifyingMap_obj (x₀ : PolarizedFamily B) (h : x₀.base = U₀.left)
    (z : (Stack.fibredCategory B S hS (yoneda.obj U₀)).val.obj) :
    (polarizedClassifyingMap B hS hT U₀ x₀ h).obj z =
      (Functor.TwoYoneda.liftBased (polarizedSliceProjection B hS hT)
        (polarizedStackUnconditional B hS hT).isFiberedInGroupoids U₀
        (polarizedFiberMk B hS hT x₀ h)).obj (Over.mk z.fiber.as) := rfl

/-- **The value of `AlgebraicGeometry.polarizedClassifyingMap` at a point of `U₀` maps to every
base change of the family along that point.** Let `z = (V, v)` be a point of `U₀` and let `w` be a
polarized family over `V` carrying a morphism `ψ : w ⟶ x₀` of polarized families lying over `v`.
Then the value of the 1-morphism named by `x₀` at `z` has a morphism to `w`: both are cartesian
lifts of `x₀` along `v`. -/
theorem nonempty_hom_polarizedClassifyingMap_obj (x₀ : PolarizedFamily B)
    (h : x₀.base = U₀.left) (z : (Stack.fibredCategory B S hS (yoneda.obj U₀)).val.obj)
    {w : PolarizedFamily B} (ψ : w ⟶ x₀)
    (hψ : (polarizedSliceProjection B hS hT).IsHomLift z.fiber.as ψ) :
    Nonempty ((polarizedClassifyingMap B hS hT U₀ x₀ h).obj z ⟶ w) :=
  Functor.TwoYoneda.nonempty_hom_liftBased_obj (polarizedSliceProjection B hS hT)
    (polarizedStackUnconditional B hS hT).isFiberedInGroupoids U₀
    (polarizedFiberMk B hS hT x₀ h) (Over.mk z.fiber.as) ψ hψ

end AlgebraicGeometry

end
