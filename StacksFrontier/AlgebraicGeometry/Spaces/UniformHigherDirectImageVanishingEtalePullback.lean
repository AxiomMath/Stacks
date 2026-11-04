module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackInjectives
public import StacksFrontier.AlgebraicGeometry.Spaces.UniformHigherDirectImageVanishing

/-!
# Uniform vanishing of higher direct images, with Stacks 03F3 part (1) supplied

`AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_of_schemeBase` and
`AlgebraicGeometry.Space.exists_forall_isZero_rightDerived_modulePushforward` reduce the uniform
vanishing of the higher direct images of [Stacks, Tag 073G] along every base change of a
quasi-compact and quasi-separated morphism of algebraic spaces to the case of a scheme base,
given that étale pullback of modules preserves injective objects — [Stacks, Tag 03F3], part (1),
for an arbitrary étale morphism of algebraic spaces. That is
`AlgebraicGeometry.Space.preservesInjectiveObjects_etaleModulePullback`, and this file states the
two reductions with it supplied.

## Main results

* `AlgebraicGeometry.Space.isZero_rightDerived_modulePushforward_of_schemeBase'`: a bound for the
  vanishing over every representable base is a bound over every base.
* `AlgebraicGeometry.Space.exists_forall_isZero_rightDerived_modulePushforward'`: the source's
  quantifier order — one degree from `f` alone, outside the base change, the module and the
  degree — granted the scheme-base case `hscheme`.

## References

* [Stacks Project, Tag 073G](https://stacks.math.columbia.edu/tag/073G)
* [Stacks Project, Tag 03F3](https://stacks.math.columbia.edu/tag/03F3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 5000] CategoryTheory.IsGrothendieckAbelian.enoughInjectives

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Reduction of the uniform vanishing of higher direct images to a representable base.** Let
`f : X ⟶ Y` be a quasi-compact and quasi-separated morphism of algebraic spaces over `S` and let
`N` bound the vanishing of the higher direct images for every base change of `f` to a
representable base, uniformly in the quasi-coherent coefficient module. Then `N` bounds it for
every base change of `f`. Part (1) of Stacks 03F3 enters through
`AlgebraicGeometry.Space.preservesInjectiveObjects_etaleModulePullback` and is not assumed. -/
theorem isZero_rightDerived_modulePushforward_of_schemeBase' {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (N : ℕ) (hscheme : SchemeBaseUniformVanishing B S hS f N)
    (Y' X' : AlgebraicSpaces B S hS) (g : Y' ⟶ Y) (i' : X' ⟶ X) (f' : X' ⟶ Y')
    (sq : IsPullback i' f' f g) (F' : Modules.{u, u} B S hS X'.1 X'.2)
    (hF' : F'.IsQuasicoherentOnSite) (q : ℕ) (hq : N ≤ q) :
    have := hasInjectiveResolutions_modules B S hS X'.1 X'.2
    IsZero (((modulePushforward B S hS f').rightDerived q).obj F') :=
  isZero_rightDerived_modulePushforward_of_schemeBase B S hS f hfqc hfqs N
    (fun _ _ i hi ↦ preservesInjectiveObjects_etaleModulePullback B S hS i hi) hscheme
    Y' X' g i' f' sq F' hF' q hq

/-- **The quantifier order of Stacks 073G, granted the scheme-base case.** Let `f : X ⟶ Y` be a
quasi-compact and quasi-separated morphism of algebraic spaces over `S`. Given a bound over
scheme bases (`hscheme`), there is a single degree `n(X → Y)` such that for every base change
`f' : X' ⟶ Y'` of `f` and every quasi-coherent `𝒪_{X'}`-module `𝓕'`, the higher direct images
`R^q f'_*𝓕'` vanish for `q ≥ n(X → Y)`. Nothing of Stacks 03F3 is assumed. -/
theorem exists_forall_isZero_rightDerived_modulePushforward' {X Y : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (hfqc : IsQuasiCompact B S hS f.hom) (hfqs : IsQuasiSeparated B S hS f.hom)
    (hscheme : ∃ N : ℕ, SchemeBaseUniformVanishing B S hS f N) :
    ∃ N : ℕ, ∀ (Y' X' : AlgebraicSpaces B S hS) (g : Y' ⟶ Y) (i' : X' ⟶ X) (f' : X' ⟶ Y'),
      IsPullback i' f' f g →
      ∀ F' : Modules.{u, u} B S hS X'.1 X'.2, F'.IsQuasicoherentOnSite → ∀ q : ℕ, N ≤ q →
        have := hasInjectiveResolutions_modules B S hS X'.1 X'.2
        IsZero (((modulePushforward B S hS f').rightDerived q).obj F') :=
  exists_forall_isZero_rightDerived_modulePushforward B S hS f hfqc hfqs
    (fun _ _ i hi ↦ preservesInjectiveObjects_etaleModulePullback B S hS i hi) hscheme

end AlgebraicGeometry.Space

end
