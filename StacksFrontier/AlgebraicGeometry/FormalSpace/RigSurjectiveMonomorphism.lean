module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigEtaleAdicMonomorphism
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveBaseChange

/-!
# Cancelling rig-surjectivity along a monomorphism

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` and `g : Y ⟶ Z` be
morphisms of locally Noetherian formal algebraic spaces over `S` which are locally of finite
type. **Stacks 0GH5** says that if `g ∘ f` is rig-surjective and `g` is a monomorphism, then
`f` is rig-surjective.

The proof is the one the source gives in a single sentence: because `g` is a monomorphism the
square with sides `𝟙 X` and `f` over `g ∘ f` and `g` is cartesian, so `f` *is* the base change
of `g ∘ f` along `g`, and rig-surjectivity is stable under base change.

## Main results

* `AlgebraicGeometry.FormalSpace.IsRigSurjective.of_comp_of_mono`: **Stacks 0GH5**.

## Implementation notes

Both inputs are already in the library and neither is carried as a hypothesis. That `f` is the
base change of `f ≫ g` along `g` when `g` is a monomorphism is
`AlgebraicGeometry.FormalSpace.isPullback_id_of_mono`, proved for the rig-étale counterpart
Stacks 0GH4; it is used in the flipped orientation
`CategoryTheory.IsPullback.flip`, which presents `f` as the first projection of the fibre
product of `g` and `f ≫ g`, since that is the slot
`AlgebraicGeometry.FormalSpace.IsRigSurjective.of_isPullback` — the library's **Stacks 0AQS**,
the Lemma 88.21.4 the source cites — asks the morphism to occupy. Local finiteness of type of
the composite, which that lemma also consumes, is
`AlgebraicGeometry.FormalSpace.IsLocallyOfFiniteType.comp`, namely Stacks 0AQ4.

A monomorphism of formal algebraic spaces over `S` is an injective map of the underlying fppf
sheaves (Stacks 0AQB), which is `CategoryTheory.Mono` in
`AlgebraicGeometry.FormalSpace.FppfSheaf`; that is the reading of Stacks 0AQB recorded in
`StacksFrontier.AlgebraicGeometry.FormalSpace.Defs` and used throughout
`StacksFrontier.AlgebraicGeometry.FormalSpace.Monomorphism`.

The locally Noetherian hypotheses on `X`, `Y` and `Z` are omitted rather than carried unused,
as in `StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjectiveBaseChange`: they enter
Definition 0AQQ only through the identification of adicness with representability by algebraic
spaces, and `AlgebraicGeometry.FormalSpace.IsRigSurjective` already takes adicness in that
representable form. Dropping them only strengthens the statement.

## References

* [Stacks Project, Tag 0AQB](https://stacks.math.columbia.edu/tag/0AQB)
* [Stacks Project, Tag 0AQQ](https://stacks.math.columbia.edu/tag/0AQQ)
* [Stacks Project, Tag 0AQS](https://stacks.math.columbia.edu/tag/0AQS)
* [Stacks Project, Tag 0GH5](https://stacks.math.columbia.edu/tag/0GH5)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0GH5.** Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of locally Noetherian formal
algebraic spaces over `S` which are locally of finite type. If `g ∘ f` is rig-surjective and
`g` is a monomorphism, then `f` is rig-surjective.

As `g` is a monomorphism, the square with sides `𝟙 X` and `f` over `g ∘ f` and `g` is
cartesian, so `f` is the base change of `g ∘ f` along `g`; and the base change of a
rig-surjective morphism locally of finite type along a morphism locally of finite type is
rig-surjective, by Stacks 0AQS. -/
@[stacks 0GH5]
theorem IsRigSurjective.of_comp_of_mono {X Y Z : FppfSheaf B S hS} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hf : IsLocallyOfFiniteType B S hS f) (hg : IsLocallyOfFiniteType B S hS g)
    (hsfg : IsRigSurjective B S hS (f ≫ g)) (hgmono : Mono g) :
    IsRigSurjective B S hS f :=
  (IsRigSurjective.of_isPullback B S hS (isPullback_id_of_mono B S hS f g hgmono).flip
    (IsLocallyOfFiniteType.comp B S hS f g hf hg) hg hsfg).2

end AlgebraicGeometry.FormalSpace

end
