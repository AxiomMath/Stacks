module

public import StacksFrontier.Algebra.Homology.DerivedCategory.BaseChangeBoundedBelow
public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionComparisonIso
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyComparison.Basic
public import StacksFrontier.Homology.DerivedIndexing.Basic

/-!
# Right acyclicity of a composite whose first factor is exact and preserves injectives

Let `F : 𝒞 ⥤ 𝒟` and `G : 𝒟 ⥤ ℰ` be additive functors between abelian categories with enough
injectives.  If `F` is exact and carries injective objects to injective objects, then the higher
right derived functors of `F ⋙ G` at an object `M` are those of `G` at `F(M)`:  an injective
resolution of `M` is carried by `F` to an injective resolution of `F(M)`, so the two complexes
whose homology computes them are the same.  In particular `F ⋙ G` is right acyclic wherever `G`
is right acyclic at `F(M)`.

This is the Grothendieck composition comparison in the only case where it degenerates
completely, and it is what makes an acyclicity statement about a *functor built by restriction
and direct image* reduce to one about direct image alone.

## Main results

* `CategoryTheory.Functor.rightAcyclic_comp_of_exact_of_preservesInjectiveObjects`:  the
  statement above.

## Implementation notes

The proof does not construct the resolution transport by hand.  Two hypotheses of
[Stacks, Tag 015M] are available for free here — `F` is right acyclic at *every* object because
it is exact (`CategoryTheory.Functor.rightAcyclic_of_exact`), and it carries injectives to
`G`-acyclic objects because it carries them to injectives
(`CategoryTheory.Functor.rightAcyclic_obj_of_preservesInjectiveObjects`) — so the collapse
isomorphism `Rⁿ(F ⋙ G)(M) ≅ RⁿG(F M)` of
`Stacks.Cohomology.AffineComparison.rightDerivedCollapseIso` applies, and right acyclicity is
read off it degree by degree through
`Stacks.DerivedIndexing.rightAcyclic_iff_forall_nat`.

That route is taken rather than the direct one through
`CategoryTheory.Functor.isIso_iff_rightAcyclic_obj_injective` because the direct one elaborates a
comparison of three right derived functors at once, which does not fit the heartbeat budget; the
`ℕ`-indexed collapse is already packaged and costs nothing.

## References

* [Stacks, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
* [Stacks, Tag 0157](https://stacks.math.columbia.edu/tag/0157)
* [Stacks, Tag 015C](https://stacks.math.columbia.edu/tag/015C)
-/

@[expose] public section

universe w w' w'' v v' v'' u u' u''

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

-- As in `StacksFrontier.Algebra.Homology.DerivedCategory.CompositionComparisonIso`:
-- `HomotopyCategory.Plus.hasPointwiseRightDerivedFunctorAt_of_injective` applies to an arbitrary
-- functor out of `K⁺(𝒜)`, so instance search reaches for it before the cheap instance coming from
-- `EnoughInjectives`, and then tries to prove termwise injectivity of an unknown complex.
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {C : Type u} {D : Type u'} {E : Type u''}
  [Category.{v} C] [Category.{v'} D] [Category.{v''} E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory.{w} C] [HasDerivedCategory.{w'} D] [HasDerivedCategory.{w''} E]
  [EnoughInjectives C] [EnoughInjectives D]

/-- **A composite whose first factor is exact and preserves injective objects is right acyclic
wherever the second factor is right acyclic at the image.**

`F` exact makes every object right acyclic for `F`, and `F` preserving injectives makes every
injective object of `𝒞` right acyclic for `G` after applying `F`; those are the two hypotheses
under which the right derived functor of the composite collapses, so
`Rⁿ(F ⋙ G)(M) ≅ RⁿG(F M)` in every degree and the vanishing above degree zero transfers. -/
theorem rightAcyclic_comp_of_exact_of_preservesInjectiveObjects
    (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] [F.PreservesInjectiveObjects]
    [PreservesFiniteLimits G] (M : C) (hG : G.rightAcyclic (F.obj M)) :
    (F ⋙ G).rightAcyclic M := by
  have hF : F.rightAcyclic M := F.rightAcyclic_of_exact M
  have hFG : ∀ I : C, Injective I → G.rightAcyclic (F.obj I) := fun I hI =>
    rightAcyclic_obj_of_preservesInjectiveObjects F G I hI
  rw [Stacks.DerivedIndexing.rightAcyclic_iff_forall_nat]
  intro n hn
  exact IsZero.of_iso
    ((Stacks.DerivedIndexing.rightAcyclic_iff_forall_nat G (F.obj M)).1 hG n hn)
    (Stacks.Cohomology.AffineComparison.rightDerivedCollapseIso F G hFG M hF n)

end CategoryTheory.Functor

end
