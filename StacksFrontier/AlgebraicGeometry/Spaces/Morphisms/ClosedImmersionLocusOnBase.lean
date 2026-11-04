module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UnramifiedLocusOnBase
public import StacksFrontier.AlgebraicGeometry.Spaces.Support.SelfProduct
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence

/-!
# The open locus on the base over which a base change is a closed immersion

Consider a commutative triangle of algebraic spaces over a scheme `S`: a morphism `f : X ⟶ Y`
together with morphisms `p : X ⟶ Z` and `q : Y ⟶ Z` such that `f ≫ q = p`. If `p` is locally
of finite type and universally closed and `q` is separated, then there is an open subspace `W`
of `Z` through which a morphism `Z' ⟶ Z` factors exactly when the base change of `f` along it
is a closed immersion. This is **Stacks 05XA**.

## Main results

* `AlgebraicGeometry.Space.universallyClosed_baseChangeOverBase`: a base change over the base
  of a universally closed morphism is universally closed.
* `AlgebraicGeometry.Space.exists_isOpenSubspace_iff_isClosedImmersion_baseChange` is
  **Stacks 05XA**.

## Implementation notes

A closed immersion is a universally closed, unramified and universally injective morphism, by
Stacks 05W8. Universal closedness holds for every base change of `f` at once: `f` is
universally closed because `p` is and `q` is separated, by part (1) of Stacks 04NX, and
universal closedness is stable under base change by Stacks 03IS. So the locus sought is the
locus of Stacks 05X9 on which the base change is unramified and universally injective, whose
hypotheses hold because a universally closed morphism is closed and because `X ×_Y X ⟶ Z` is
the composition of the universally closed `X ×_Y X ⟶ X` — a base change of `f` — with `p`, by
the universally closed case of Stacks 03IU.

## References

* [Stacks Project, Tag 05XA](https://stacks.math.columbia.edu/tag/05XA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A base change of a universally closed morphism `f : X ⟶ Y` of algebraic spaces over `S`
along a morphism to a space `Z` under which `X` and `Y` both lie is universally closed.

The square exhibiting `AlgebraicGeometry.Space.baseChangeOverBase` as a base change of `f` is
cartesian, and universal closedness transfers along a cartesian square by Stacks 03IS. -/
theorem universallyClosed_baseChangeOverBase (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (p : X ⟶ Z)
    (q : Y ⟶ Z) (hfq : f ≫ q = p) (hf : UniversallyClosed B S hS f)
    {Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hZ' : IsAlgebraicSpace B S hS Z') (g : Z' ⟶ Z) :
    UniversallyClosed B S hS (baseChangeOverBase B S hS f p q hfq g) :=
  universallyClosed_of_isPullback B S hS (isAlgebraicSpace_pullback B S hS p g hX hZ' hZ) hX
    (isAlgebraicSpace_pullback B S hS q g hY hZ' hZ) hY f (pullback.fst q g) hf
    (isPullback_baseChangeOverBase B S hS f p q hfq g).flip

/-- **Stacks 05XA.** Let `f : X ⟶ Y` be a morphism of algebraic spaces over `S` whose source and
target are given over a third algebraic space `Z` by morphisms `p : X ⟶ Z` and `q : Y ⟶ Z` with
`f ≫ q = p`. If `p` is locally of finite type and universally closed and `q` is separated, then
there is an open subspace `W` of `Z` through which a morphism `Z' ⟶ Z` from an algebraic space
factors exactly when the base change of `f` along it is a closed immersion.

The open subspace is the one of Stacks 05X9 for the same triangle, over which the base change
of `f` is unramified and universally injective: it is available because `p` is closed and
because `X ×_Y X ⟶ Z` is closed, being a base change of `f` followed by `p`. Every base change
of `f` is universally closed, since `f` is by part (1) of Stacks 04NX, so the three conditions
of Stacks 05W8 for the base change reduce to the two cut out by that subspace. -/
@[stacks 05XA]
theorem exists_isOpenSubspace_iff_isClosedImmersion_baseChange
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (p : X ⟶ Z) (q : Y ⟶ Z) (hfq : f ≫ q = p)
    (hp : IsLocallyOfFiniteType B S hS p) (hpuc : UniversallyClosed B S hS p)
    (hq : IsSeparated B S hS q) :
    ∃ W : Subfunctor Z, IsOpenSubspace B S hS W ∧
      ∀ (Z' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_ : IsAlgebraicSpace B S hS Z') (g : Z' ⟶ Z),
        (∃ r : Z' ⟶ W.toFunctor, r ≫ W.ι = g) ↔
          IsClosedImmersion B S hS (baseChangeOverBase B S hS f p q hfq g) := by
  have hfuc : UniversallyClosed B S hS f :=
    universallyClosed_of_comp_of_isSeparated B S hS hX hY hZ f q
      (by rw [hfq]; exact hpuc) hq
  have hp₂ : IsClosedMorphism B S hS (pullback.fst f f ≫ p) :=
    isClosed_of_universallyClosed B S hS hZ _
      (universallyClosed_comp B S hS hX hZ (pullback.fst f f) p
        (universallyClosed_pullback B S hS f f hfuc) hpuc)
  obtain ⟨W, hWopen, hW⟩ :=
    exists_isOpenSubspace_iff_isUnramified_universallyInjective_baseChange B S hS hX hY hZ
      f p q hfq hp (isClosed_of_universallyClosed B S hS hZ p hpuc) hp₂
  refine ⟨W, hWopen, fun Z' hZ' g ↦ (hW Z' hZ' g).trans ?_⟩
  have htfae := (closedImmersion_conditions_tfae B S hS
    (isAlgebraicSpace_pullback B S hS p g hX hZ' hZ)
    (isAlgebraicSpace_pullback B S hS q g hY hZ' hZ)
    (baseChangeOverBase B S hS f p q hfq g)).out 3 1
  exact ⟨fun h ↦ htfae.mp ⟨universallyClosed_baseChangeOverBase B S hS hX hY hZ f p q hfq
    hfuc hZ' g, h⟩, fun h ↦ (htfae.mpr h).2⟩

end AlgebraicGeometry.Space

end
