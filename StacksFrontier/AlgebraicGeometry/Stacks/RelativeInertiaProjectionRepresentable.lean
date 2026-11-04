module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.BaseChange
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDiagonalSquare
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityPostcomp
public import StacksFrontier.AlgebraicGeometry.Stacks.RepresentabilityTransport
public import StacksFrontier.CategoryTheory.FiberedCategory.InertiaBasedCategory
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverCompare
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.SecondDiagonal

/-!
# The projection of the relative inertia is representable by algebraic spaces (Stacks 050Q)

Let `S` be a scheme contained in a big fppf site `B`, let `𝒳` and `𝒴` be categories fibred in
groupoids over the big fppf site of `S` whose diagonals are representable by algebraic spaces —
condition (1) of Stacks 045G, the second clause of being an algebraic stack — and let
`f : 𝒳 ⟶ 𝒴` be a 1-morphism. Then the forgetful 1-morphism `π : I_{𝒳/𝒴} ⟶ 𝒳` of the relative
inertia is representable by algebraic spaces. This is the relative half of Stacks 050Q; the
absolute half is `StacksFrontier.AlgebraicGeometry.Stacks.InertiaProjectionRepresentable`.

The proof is the source's, in three steps.

1. The projection `𝒳 ×_𝒴 𝒳 ⟶ 𝒳 × 𝒳` is a base change of the diagonal of `𝒴`, by the
   over-the-site form of Stacks 02XE
   (`AlgebraicGeometry.Stack.relativeDiagonalSquare`), so Stacks 0302 makes it representable by
   algebraic spaces.
2. The relative diagonal `Δ_f : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` composed with that projection is the absolute
   diagonal of `𝒳`, which is representable by hypothesis; so `Δ_f` is representable by the
   cancellation of a representable postcomposition,
   `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_postcomp`.
3. By Stacks 034H (1) the relative inertia is the second 2-fibre product of `Δ_f`, and `π` is
   the first projection of a 2-fibre product square over the cospan `(Δ_f, Δ_f)`, hence a base
   change of `Δ_f`; Stacks 0302 again, transported along the equivalence of Stacks 034H (1) by
   Stacks 0457.

## Main results

* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_twoFibreProductProjection`: step 1.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_relativeDiagonal`: step 2, the
  representability of the relative diagonal.
* `AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_relativeInertiaProjection`:
  **Stacks 050Q** for the relative inertia, from the representability of the two diagonals
  alone.
* `isRepresentableByAlgebraicSpaces_relativeInertiaProjection_of_isAlgebraicStack`, in the same
  namespace: the same for a 1-morphism of algebraic stacks, which is the form **Stacks 050Q**
  states.

## Implementation notes

The source's statement of Stacks 050Q also asserts that the relative inertia *is* an algebraic
stack and that `π` is locally of finite type. Neither is proved here; the tag carries the
quoted sub-claim this file does prove, as the absolute half does.

The universes are the saturated ones Stacks 0302 forces,
`CatFiberedInGroupoids.{u, max u v, u + 1, max (max (u + 1) w) v}`, and both universe arguments
of Stacks 0302 are passed explicitly at each use, since `max` to the right of a universe
metavariable is not solvable by unification. At those universes `𝒳 × 𝒳`, `𝒴 × 𝒴`,
`𝒳 ×_𝒴 𝒳` and the relative inertia are all objects of the same 2-category as `𝒳` and `𝒴`.

## References

* [Stacks Project, Tag 050Q](https://stacks.math.columbia.edu/tag/050Q)
* [Stacks Project, Tag 02XE](https://stacks.math.columbia.edu/tag/02XE)
* [Stacks Project, Tag 034H](https://stacks.math.columbia.edu/tag/034H)
* [Stacks Project, Tag 0302](https://stacks.math.columbia.edu/tag/0302)
* [Stacks Project, Tag 045G](https://stacks.math.columbia.edu/tag/045G)
* [Stacks Project, Tag 0457](https://stacks.math.columbia.edu/tag/0457)
-/

@[expose] public section

open CategoryTheory

namespace AlgebraicGeometry.Stack

universe u v w t

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The projection of a 2-fibre product to the product is a base change of the diagonal.**
For 1-morphisms `x : 𝒯₁ ⟶ 𝒳` and `y : 𝒯₂ ⟶ 𝒳` of categories fibred in groupoids over the big
fppf site of `S`, the projection `𝒯₁ ×_𝒳 𝒯₂ ⟶ 𝒯₁ × 𝒯₂` is representable by algebraic spaces as
soon as the diagonal of `𝒳` is — condition (1) of Stacks 045G, the second clause of being an
algebraic stack.

This is Stacks 0302 applied to `AlgebraicGeometry.Stack.relativeDiagonalSquare`, the
over-the-site form of Stacks 02XE. -/
theorem isRepresentableByAlgebraicSpaces_twoFibreProductProjection
    (𝒯₁ 𝒯₂ 𝒳 : CatFiberedInGroupoids.{u, max u v, u + 1, max (max (u + 1) w) v}
      (BigFppfOver B S hS))
    (x : 𝒯₁ ⟶ 𝒳) (y : 𝒯₂ ⟶ 𝒳)
    (hΔ : IsRepresentableByAlgebraicSpaces B S hS (diagonalBasedFunctor B S hS 𝒳)) :
    IsRepresentableByAlgebraicSpaces B S hS
      (relativeDiagonalSquare B S hS 𝒯₁ 𝒯₂ 𝒳 x y).fst.hom :=
  isRepresentableByAlgebraicSpaces_baseChange.{u, v, w} B S hS 𝒳
    (CatFiberedInGroupoids.product 𝒳 𝒳) (CatFiberedInGroupoids.product 𝒯₁ 𝒯₂)
    (diagonal B S hS 𝒳) (CatFiberedInGroupoids.productMap x y)
    (relativeDiagonalSquare B S hS 𝒯₁ 𝒯₂ 𝒳 x y)
    (isTwoFibreProduct_relativeDiagonalSquare B S hS 𝒯₁ 𝒯₂ 𝒳 x y) hΔ

/-- **The relative diagonal of a 1-morphism is representable by algebraic spaces.** If the
diagonals of `𝒳` and of `𝒴` are representable by algebraic spaces, then so is the relative
diagonal `Δ_f : 𝒳 ⟶ 𝒳 ×_𝒴 𝒳` of a 1-morphism `f : 𝒳 ⟶ 𝒴`.

The relative diagonal lies over `𝒳 × 𝒳`: composing it with the projection
`𝒳 ×_𝒴 𝒳 ⟶ 𝒳 × 𝒳` gives the absolute diagonal of `𝒳` on the nose. The projection is
representable by `isRepresentableByAlgebraicSpaces_twoFibreProductProjection` and the absolute
diagonal by hypothesis, so
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_of_postcomp` applies. -/
theorem isRepresentableByAlgebraicSpaces_relativeDiagonal
    (𝒳 𝒴 : CatFiberedInGroupoids.{u, max u v, u + 1, max (max (u + 1) w) v}
      (BigFppfOver B S hS))
    (f : 𝒳 ⟶ 𝒴)
    (hΔ𝒳 : IsRepresentableByAlgebraicSpaces B S hS (diagonalBasedFunctor B S hS 𝒳))
    (hΔ𝒴 : IsRepresentableByAlgebraicSpaces B S hS (diagonalBasedFunctor B S hS 𝒴)) :
    IsRepresentableByAlgebraicSpaces B S hS (relativeDiagonalBasedFunctor B S hS 𝒳 𝒴 f.hom) :=
  isRepresentableByAlgebraicSpaces_of_postcomp B S hS
    (relativeDiagonalSquare B S hS 𝒳 𝒳 𝒴 f f).fst.hom
    (diagonalBasedFunctor B S hS 𝒳)
    (relativeDiagonalBasedFunctor B S hS 𝒳 𝒴 f.hom)
    (Iso.refl _)
    (isRepresentableByAlgebraicSpaces_twoFibreProductProjection B S hS 𝒳 𝒳 𝒴 f f hΔ𝒴)
    hΔ𝒳

/-- **Stacks 050Q for the relative inertia.** If the diagonals of `𝒳` and of `𝒴` are
representable by algebraic spaces, then the forgetful 1-morphism
`π : I_{𝒳/𝒴} ⟶ 𝒳` of the relative inertia of a 1-morphism `f : 𝒳 ⟶ 𝒴` is representable by
algebraic spaces.

The proof is the source's. By Stacks 034H (1) the relative inertia is the second 2-fibre product
of the relative diagonal,

```text
I_{𝒳/𝒴} ≃ 𝒳 ×_{Δ_f, 𝒳 ×_𝒴 𝒳, Δ_f} 𝒳       over the big fppf site of `S`,
```

and under that equivalence `π` is the first projection of a 2-fibre product square over the
cospan `(Δ_f, Δ_f)`, hence a base change of `Δ_f`; so Stacks 0302 applies, `Δ_f` being
representable by `isRepresentableByAlgebraicSpaces_relativeDiagonal`. The equivalence is
`CategoryTheory.TwoFibreProductOver.isEquivalenceOver_toRelativeInertia` and the transport of
representability along an equivalence of the source is Stacks 0457 in the form
`AlgebraicGeometry.Stack.isRepresentableByAlgebraicSpaces_iff_of_equivalence_source`. -/
theorem isRepresentableByAlgebraicSpaces_relativeInertiaProjection
    (𝒳 𝒴 : CatFiberedInGroupoids.{u, max u v, u + 1, max (max (u + 1) w) v}
      (BigFppfOver B S hS))
    (f : 𝒳 ⟶ 𝒴)
    (hΔ𝒳 : IsRepresentableByAlgebraicSpaces B S hS (diagonalBasedFunctor B S hS 𝒳))
    (hΔ𝒴 : IsRepresentableByAlgebraicSpaces B S hS (diagonalBasedFunctor B S hS 𝒴)) :
    IsRepresentableByAlgebraicSpaces B S hS (RelativeInertia.basedProjection f.hom) := by
  set P := CatFiberedInGroupoids.twoFibreProductSquare.{u, v, u + 1, w}
    (relativeDiagonal B S hS 𝒳 𝒴 f) (relativeDiagonal B S hS 𝒳 𝒴 f)
  have h₁ : IsRepresentableByAlgebraicSpaces B S hS P.fst.hom :=
    isRepresentableByAlgebraicSpaces_baseChange.{u, v, w} B S hS 𝒳
      (twoFibreProduct B S hS 𝒴 𝒳 𝒳 f.hom f.hom) 𝒳
      (relativeDiagonal B S hS 𝒳 𝒴 f) (relativeDiagonal B S hS 𝒳 𝒴 f) P
      (CatFiberedInGroupoids.isTwoFibreProduct_twoFibreProductSquare.{u, v, u + 1, w}
        (relativeDiagonal B S hS 𝒳 𝒴 f) (relativeDiagonal B S hS 𝒳 𝒴 f))
      (isRepresentableByAlgebraicSpaces_relativeDiagonal B S hS 𝒳 𝒴 f hΔ𝒳 hΔ𝒴)
  obtain ⟨E⟩ := TwoFibreProductOver.isEquivalenceOver_toRelativeInertia f.hom.w
  have hinertia : (RelativeInertia.basedCategory f.hom).p.IsFiberedInGroupoids :=
    StacksRepresentableCFG.isFiberedInGroupoids_of_equivalenceOver
      (StacksRepresentableCFG.EquivalenceOver.ofIsEquivalenceOver E).symm P.pt.isFiberedInGroupoids
  let aFun : (RelativeInertia.basedCategory f.hom) ⥤ᵇ P.pt.val :=
    ⟨TwoFibreProductOver.ofRelativeInertia f.hom.w,
      TwoFibreProductOver.ofRelativeInertia_comp_structureFunctor f.hom.w⟩
  have hequiv : Functor.IsEquivalence aFun.toFunctor :=
    (CategoryTheory.Equivalence.mk (TwoFibreProductOver.ofRelativeInertia f.hom.w)
      (TwoFibreProductOver.toRelativeInertia f.hom.w)
      (eqToIso (TwoFibreProductOver.ofRelativeInertia_comp_toRelativeInertia f.hom.w).symm)
      (TwoFibreProductOver.unitIso f.hom.w).symm).isEquivalence_functor
  exact (isRepresentableByAlgebraicSpaces_iff_of_equivalence_source B S hS
    (𝒳' := CatFiberedInGroupoids.mk _ hinertia) (𝒳 := P.pt) (𝒴 := 𝒳)
    P.fst.hom (RelativeInertia.basedProjection f.hom) aFun (Iso.refl _)).mp h₁

/-- **Stacks 050Q for the relative inertia of a morphism of algebraic stacks.** The forgetful
1-morphism `π : I_{𝒳/𝒴} ⟶ 𝒳` of the relative inertia of a 1-morphism of algebraic stacks is
representable by algebraic spaces. Only the representability of the two diagonals — the second
clause of `AlgebraicGeometry.Stack.IsAlgebraicStack` — is used.

The source's statement also asserts that `I_{𝒳/𝒴}` is an algebraic stack and that `π` is
locally of finite type; neither is proved here. -/
@[stacks 050Q "representability by algebraic spaces of the relative inertia projection"]
theorem isRepresentableByAlgebraicSpaces_relativeInertiaProjection_of_isAlgebraicStack
    (𝒳 𝒴 : CatFiberedInGroupoids.{u, max u v, u + 1, max (max (u + 1) w) v}
      (BigFppfOver B S hS))
    (f : 𝒳 ⟶ 𝒴)
    (h𝒳 : IsAlgebraicStack.{u, t} B S hS 𝒳.val)
    (h𝒴 : IsAlgebraicStack.{u, t} B S hS 𝒴.val) :
    IsRepresentableByAlgebraicSpaces B S hS (RelativeInertia.basedProjection f.hom) := by
  obtain ⟨_, -, hΔ𝒳, -⟩ := h𝒳
  obtain ⟨_, -, hΔ𝒴, -⟩ := h𝒴
  exact isRepresentableByAlgebraicSpaces_relativeInertiaProjection B S hS 𝒳 𝒴 f hΔ𝒳 hΔ𝒴

end AlgebraicGeometry.Stack

end
