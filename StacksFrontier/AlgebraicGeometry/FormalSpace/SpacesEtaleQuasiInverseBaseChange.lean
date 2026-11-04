module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SpacesEtaleQuasiInverse
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DependentProduct.Basic
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DependentProduct.BaseChange
public import StacksFrontier.AlgebraicGeometry.FormalSpace.DependentProduct.Universal

/-!
# Base change of the quasi-inverse `U_{V, ψ}` of Stacks 0DEG

Let `S` be a scheme contained in a big fppf site `B`. The functor `U_{V, ψ}` of the proof of
Stacks 0DEG is constructed in
`StacksFrontier/AlgebraicGeometry/FormalSpace/SpacesEtaleQuasiInverse.lean` for an arbitrary pair
of morphisms of fppf sheaves `i : I ⟶ X` and `p : W ⟶ I`, as the dependent product (Weil
restriction) `AlgebraicGeometry.FormalSpace.liftAlong` of `p` along `i`.

This file proves that the construction commutes with base change: for a cartesian square whose
sides are `i' : I' ⟶ X'`, `g : I' ⟶ I`, `f : X' ⟶ X` and `i : I ⟶ X`, and for `p : W ⟶ I`
with its base change `p' : W' ⟶ I'`, the square whose sides are the comparison morphism
`liftAlong i' p' ⟶ liftAlong i p`, the two structure morphisms to `X'` and `X`, and `f`, is
again cartesian. This is the Beck–Chevalley isomorphism for the dependent product, and it is
the step of the proof of Stacks 0DEG which identifies `U_{V, ψ} ×_X X_i` with
`U_{V_i, ψ_i}` for a chart `X_i ⟶ X`: the source says "we obtain
`U_{V, ψ} ×_X X_i = U_{V_i, ψ_i}`, where `V_i = V ×_{X_red} X_{i, red}`, using that
`X_{i, red} = X_i ×_X X_red`".

## Main definitions

* `AlgebraicGeometry.FormalSpace.IsSectionwisePullback`: a commuting square of fppf sheaves is
  cartesian on sections over every object of the site. Every cartesian square is one
  (`AlgebraicGeometry.FormalSpace.isSectionwisePullback_of_isPullback`), and this is the form in
  which cartesianness is consumed below, the whole argument being a chase on sections.
* `AlgebraicGeometry.FormalSpace.liftAlongBaseChange`: the comparison morphism
  `U_{V', ψ'} ⟶ U_{V, ψ}` attached to a cartesian change of base.
* `AlgebraicGeometry.FormalSpace.bcPointSection`: the morphism `I' ⟶ Wt` over `I` that a point
  `X' ⟶ U_{Wt, pt}` of a dependent product determines, `I'` being the fibre product
  `X' ×_X I`.

## Main results

* `AlgebraicGeometry.FormalSpace.liftAlongBaseChange_comp_liftAlongBase`: the comparison
  morphism lies over `f : X' ⟶ X`.
* `AlgebraicGeometry.FormalSpace.isPullback_liftAlongMap`: the comparison square is cartesian
  over an arbitrary point of a dependent product, not only over a point of `X`. This is the
  Beck–Chevalley isomorphism and the preservation of fibre products by the dependent product at
  once, and it is the general statement proved here.
* `AlgebraicGeometry.FormalSpace.isPullback_liftAlongBaseChange`: the comparison square is
  cartesian, that is `U_{V', ψ'} = X' ×_X U_{V, ψ}`. This is the case `pt = 𝟙 I` of the
  previous statement, the dependent product of the identity being `X` itself
  (`AlgebraicGeometry.FormalSpace.isIso_liftAlongBase_id`).

## Implementation notes

The general square is stated for a morphism `k : W ⟶ Wt` over `I` and a point
`σ : X' ⟶ U_{Wt, pt}`: the dependent product along `i` is right adjoint to the base change
along `i`, so it carries the fibre product of `W` with `I'` over `Wt` — the fibre product of
the sheaves over `I` that `k` and `AlgebraicGeometry.FormalSpace.bcPointSection` present — to
the fibre product of `U_{W, p}` with `X'` over `U_{Wt, pt}`. Base change along a morphism
`f : X' ⟶ X` is the case `pt = 𝟙 I`, where a point of the dependent product of the identity is
just a morphism to `X`; so there is one chase here and not two.

Everything is a chase on sections. A section of `liftAlong i p` over `T` is a section `a` of
`X` together with a rule `b` assigning an element of `W` to every pair consisting of a morphism
`t : T' ⟶ T` of the site and a section `w` of `I` over `T'` with `i(w) = t^* a`; such a pair is
exactly a section of the fibre product `T' ×_{t^* a, X} I`. Pushing a section of
`liftAlong i' p'` forward replaces the section `a'` of `X'` by `f(a')` and transports the rule
by sending a pair `(t, w)` over `X` to the unique pair above it over `X'`, which the
cartesianness of the square of `I'` provides; pulling a section back reverses this, using the
cartesianness of the square of `W'`. The compatibility conditions of a section, the naturality
of the two constructions and the uniqueness half of the universal property all reduce to the
uniqueness halves of those two cartesian squares, which is why no gluing and no sheaf condition
is used here.

The cartesian square is produced from `CategoryTheory.Limits.PullbackCone.IsLimit.mk` directly
in the category of fppf sheaves, exactly as
`AlgebraicGeometry.FormalSpace.isPullback_liftAlongSection` is.

## References

* [Stacks Project, Tag 0DEG](https://stacks.math.columbia.edu/tag/0DEG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

open AlgebraicGeometry.FormalSpace.DependentProduct

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Cartesian squares, read on sections -/

/-! ### The comparison morphism -/

section BaseChange

variable {B S hS} {X X' I I' W W' : FppfSheaf B S hS}
  {i : I ⟶ X} {i' : I' ⟶ X'} {f : X' ⟶ X} {g : I' ⟶ I}
  {p : W ⟶ I} {p' : W' ⟶ I'} (q : W' ⟶ W)

/-! #### Pushing a section forward -/

variable (hIex : IsSectionwisePullback B S hS i' g f i)

/-! #### The compatibility a section of `I'` provides -/

/-! #### The point of `Wt` over `I'` determined by a point of the dependent product -/

section Point

variable {Wt : FppfSheaf B S hS} {pt : Wt ⟶ I} {σ : X' ⟶ liftAlong B S hS i pt}
  (hσ : σ ≫ liftAlongBase B S hS i pt = f) (hcomm : i' ≫ f = g ≫ i)

end Point

/-! #### Pulling a section back -/

section Cone

variable {Wt : FppfSheaf B S hS} {pt : Wt ⟶ I} {k : W ⟶ Wt} (hk : k ≫ pt = p)
  {σ : X' ⟶ liftAlong B S hS i pt} (hσ : σ ≫ liftAlongBase B S hS i pt = f)
  (hcomm : i' ≫ f = g ≫ i)
  (hWex : IsSectionwisePullback B S hS q p' k (bcPointSection hσ hcomm))
  (hcommW : q ≫ k = p' ≫ bcPointSection hσ hcomm)
  {Z : FppfSheaf B S hS} (α : Z ⟶ liftAlong B S hS i p) (β : Z ⟶ X')
  (hαβ : α ≫ liftAlongMap B S hS i k hk = β ≫ σ)

end Cone

section Square

variable {Wt : FppfSheaf B S hS} {pt : Wt ⟶ I} {k : W ⟶ Wt} (hk : k ≫ pt = p)
  {σ : X' ⟶ liftAlong B S hS i pt} (hσ : σ ≫ liftAlongBase B S hS i pt = f)
  (hcomm : i' ≫ f = g ≫ i)
  (hWex : IsSectionwisePullback B S hS q p' k (bcPointSection hσ hcomm))
  (hcommW : q ≫ k = p' ≫ bcPointSection hσ hcomm)

end Square

end BaseChange

end AlgebraicGeometry.FormalSpace

end
