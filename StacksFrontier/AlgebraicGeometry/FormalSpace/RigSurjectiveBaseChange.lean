module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RigSurjective

/-!
# Rig-surjectivity is stable under base change

Let `S` be a scheme contained in a big fppf site `B` and let `f : X ⟶ Y` and `g : Z ⟶ Y` be
morphisms of locally Noetherian formal algebraic spaces over `S` which are locally of finite
type. **Stacks 0AQS** says that if `f` is rig-surjective then so is the base change
`Z ×_Y X ⟶ Z`.

## Main results

* `AlgebraicGeometry.FormalSpace.IsRigSurjective.of_isPullback`: **Stacks 0AQS**.
* `AlgebraicGeometry.FormalSpace.IsRigSurjective.pullback_fst`: the same statement for the
  chosen fibre product, which is the shape the source states.

## Implementation notes

The proof is the one the source calls straightforward. An adic point `p : Spf R ⟶ Z` of the
base, `R` a complete discrete valuation ring, is pushed to an adic point `p ≫ g` of `Y`:
adicness is representability by algebraic spaces (Stacks 0AQ3) and `g`, being locally of finite
type, is representable by Definition 0AM4, so the composite is representable by Stacks 0APY.
Rig-surjectivity of `f` then supplies an extension `R ⊂ R'` of complete discrete valuation
rings and a lift `x : Spf R' ⟶ X` of `Spf R' ⟶ Spf R ⟶ Z ⟶ Y` through `f`; the pair
`(Spf R' ⟶ Spf R ⟶ Z, x)` is a point of the fibre product over `Z`, which is the required lift.

The source cites Formal Spaces, Lemmas 87.24.4 and 87.24.9, that is **Stacks 0AQ5** and
**Stacks 0AQ8**. They are what makes the conclusion an instance of Definition 0AQQ at all,
that definition presupposing its morphism to be locally of finite type between locally
Noetherian formal algebraic spaces. Stacks 0AQ5 is `IsLocallyOfFiniteType.of_isPullback` and
is therefore recorded here as the first half of the conclusion, exactly as Stacks 0AQ4 is
recorded in `AlgebraicGeometry.FormalSpace.IsRigSurjective.comp`. Stacks 0AQ8, that `Z ×_Y X`
is locally Noetherian, lives in
`StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteTypeNoetherian` and is not restated: it is a
property of the fibre product rather than of the projection, and the predicate
`AlgebraicGeometry.FormalSpace.IsRigSurjective` does not consume it.

The statement is made for an arbitrary cartesian square rather than for the chosen fibre
product, as Stacks 0AQ5 is in this library, so that it applies to any presentation of
`Z ×_Y X`; the form the source states is the corollary
`AlgebraicGeometry.FormalSpace.IsRigSurjective.pullback_fst`.

The locally Noetherian hypotheses on `X`, `Y` and `Z` are not used: they enter Definition 0AQQ
only through the identification of adicness with representability, which the predicate already
takes in the representable form. They are therefore omitted rather than carried unused, as
elsewhere in this part of the library.

## References

* [Stacks Project, Tag 0AQ3](https://stacks.math.columbia.edu/tag/0AQ3)
* [Stacks Project, Tag 0AQ5](https://stacks.math.columbia.edu/tag/0AQ5)
* [Stacks Project, Tag 0AQ8](https://stacks.math.columbia.edu/tag/0AQ8)
* [Stacks Project, Tag 0AQQ](https://stacks.math.columbia.edu/tag/0AQQ)
* [Stacks Project, Tag 0AQS](https://stacks.math.columbia.edu/tag/0AQS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0AQS.** Let `f : X ⟶ Y` and `g : Z ⟶ Y` be morphisms of formal algebraic spaces
over `S` which are locally of finite type. A base change `p : W ⟶ Z` of `f` along `g` is
locally of finite type, and is rig-surjective as soon as `f` is.

An adic point of `Z` out of the formal spectrum of a complete discrete valuation ring becomes,
after composition with `g`, an adic point of `Y`, because `g` is representable by algebraic
spaces; a lift of it to `X` over an extension of complete discrete valuation rings pairs with
the point of `Z` to give a lift to `W`. -/
@[stacks 0AQS]
theorem IsRigSurjective.of_isPullback {W X Y Z : FppfSheaf B S hS}
    {p : W ⟶ Z} {q : W ⟶ X} {g : Z ⟶ Y} {f : X ⟶ Y} (sq : IsPullback p q g f)
    (hf : IsLocallyOfFiniteType B S hS f) (hg : IsLocallyOfFiniteType B S hS g)
    (hsf : IsRigSurjective B S hS f) :
    IsLocallyOfFiniteType B S hS p ∧ IsRigSurjective B S hS p := by
  refine ⟨IsLocallyOfFiniteType.of_isPullback B S hS sq hf, ?_⟩
  intro R _ _ _ _ _ _ hRadic hRcomplete hRweak D pt hpt
  obtain ⟨hgrep, -⟩ := hg
  obtain ⟨R', hR'ring, hR'dom, hR'dvr, hR'alg, hR'ext, hR'top, hR'topring, hR'lin, hR'adic,
    hR'complete, D', e, x, he, hx⟩ :=
    hsf R hRadic hRcomplete hRweak D (pt ≫ g)
      (Space.isRepresentableByAlgebraicSpacesULift_comp B S hS pt.hom g.hom hpt hgrep)
  refine ⟨R', hR'ring, hR'dom, hR'dvr, hR'alg, hR'ext, hR'top, hR'topring, hR'lin, hR'adic,
    hR'complete, D', e,
    sq.lift (formalSpectrumMap hRweak e ≫ pt) x (by rw [Category.assoc]; exact hx.symm),
    he, sq.lift_fst _ _ _⟩

/-- **Stacks 0AQS** for the chosen fibre product, which is the shape the source states: if
`f : X ⟶ Y` and `g : Z ⟶ Y` are locally of finite type and `f` is rig-surjective, then
`Z ×_Y X ⟶ Z` is locally of finite type and rig-surjective. -/
theorem IsRigSurjective.pullback_fst {X Y Z : FppfSheaf B S hS} (g : Z ⟶ Y) (f : X ⟶ Y)
    [HasPullback g f] (hf : IsLocallyOfFiniteType B S hS f)
    (hg : IsLocallyOfFiniteType B S hS g) (hsf : IsRigSurjective B S hS f) :
    IsLocallyOfFiniteType B S hS (pullback.fst g f) ∧
      IsRigSurjective B S hS (pullback.fst g f) :=
  IsRigSurjective.of_isPullback B S hS (IsPullback.of_hasPullback g f) hf hg hsf

end AlgebraicGeometry.FormalSpace

end
