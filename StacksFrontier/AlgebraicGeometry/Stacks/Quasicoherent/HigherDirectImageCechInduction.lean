module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.HigherDirectImageCechStep
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.CechTermAlgebraicStack

/-!
# The inductive step of the proof of Stacks 076Z

Let `M` be a rule satisfying hypotheses (1) and (2) of **Stacks 076Z**, let `f : 𝒳 ⟶ 𝒴` be a
`1`-morphism of algebraic stacks and let `c : 𝒰 ⟶ 𝒳` be representable by algebraic spaces,
surjective and smooth. If the higher direct images along every composite `𝒰ₙ ⟶ 𝒳 ⟶ 𝒴` of a
projection of the relative Čech nerve of `c` with `f` carry `M` into `M`, then so do the higher
direct images along `f`.

## Main definitions

* `AlgebraicGeometry.Stack.StackEtaleModuleRule.strictChart`: the chart `c`, retargeted at the
  strict presentation of `𝒳` by `f`.

## Main results

* `AlgebraicGeometry.Stack.StackEtaleModuleRule.preservedBy_of_cechTerms`: the inductive step of
  **Stacks 076Z**.

## References

* [Stacks Project, Tag 076Z](https://stacks.math.columbia.edu/tag/076Z)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u t

namespace AlgebraicGeometry.Stack.StackEtaleModuleRule

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒰 𝒳 𝒴 : AlgebraicStacks.{u, t} B S hS} (c : 𝒰 ⟶ 𝒳) (f : 𝒳 ⟶ 𝒴)

/-- The chart `c`, retargeted at the strict presentation of `𝒳` by `f`. -/
abbrev strictChart : 𝒰 ⟶ AlgebraicStacks.strictSource B S hS f :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    ⟨c.hom.hom.toFunctor, by
      change CatFiberedInGroupoids.homFunctor c.hom ⋙
        CatFiberedInGroupoids.homFunctor f.hom ⋙ 𝒴.val.val.p = 𝒰.val.val.p
      rw [CatFiberedInGroupoids.homFunctor_comp_p, CatFiberedInGroupoids.homFunctor_comp_p]⟩)

/-- The identity functor, as a 1-morphism from `𝒳` to its strict presentation by `f`. -/
abbrev toStrictSource : 𝒳 ⟶ AlgebraicStacks.strictSource B S hS f :=
  Bicategory.InducedBicategory.mkHom (Bicategory.InducedBicategory.mkHom
    ⟨𝟭 _, CatFiberedInGroupoids.homFunctor_comp_p f.hom⟩)

/-- The retargeted chart is smooth when `c` is. -/
theorem isSmooth_strictChart (hc : AlgebraicStacks.IsSmooth B S hS c) :
    AlgebraicStacks.IsSmooth B S hS (strictChart B S hS c f) :=
  AlgebraicStacks.isSmooth_of_twoIso B S hS (Iso.refl _)
    (AlgebraicStacks.isSmooth_comp B S hS c (toStrictSource B S hS f) hc
      (AlgebraicStacks.isSmooth_of_isEquivalence B S hS _
        (inferInstanceAs (𝟭 _).IsEquivalence)))

/-- **The inductive step of Stacks 076Z.** Let `M` satisfy hypotheses (1) and (2) of
**Stacks 076Z**, let `c : 𝒰 ⟶ 𝒳` be representable by algebraic spaces, surjective and smooth,
and let `f : 𝒳 ⟶ 𝒴`. If every higher direct image along every composite of a projection
`𝒰ₙ ⟶ 𝒳` of the relative Čech nerve of `c` with `f` carries `M` into `M`, then so does every
higher direct image along `f`. -/
theorem preservedBy_of_cechTerms (M : StackEtaleModuleRule B S hS)
    (hserre : IsWeakSerre.{u, t} B S hS M)
    (hpull : IsStableUnderSmoothPullback.{u, t} B S hS M)
    (hrep : Stack.IsRepresentableByAlgebraicSpaces B S hS c.hom.hom)
    (hsurj : Stack.IsSurjective B S hS c) (hsmooth : AlgebraicStacks.IsSmooth B S hS c)
    (hterms : ∀ n i : ℕ, PreservedBy B S hS M
      (AlgebraicStacks.cechProjection B S hS (strictChart B S hS c f) n ≫
        AlgebraicStacks.strictHom B S hS f) i)
    (i : ℕ) : PreservedBy B S hS M f i := fun F hF =>
  mem_higherDirectImage_of_cechPages B S hS c f M hserre hrep hsurj hsmooth F
    (fun p q => hterms p q _
      (hpull (AlgebraicStacks.cechProjection B S hS (strictChart B S hS c f) p)
        (AlgebraicStacks.isSmooth_cechProjection B S hS _
          (isSmooth_strictChart B S hS c f hsmooth) p) F hF)) i

end AlgebraicGeometry.Stack.StackEtaleModuleRule

end
