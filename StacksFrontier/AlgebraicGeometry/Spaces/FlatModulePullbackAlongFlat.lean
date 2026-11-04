module

public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModuleAllPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModulePullbackPermanence

/-!
# Relative flatness is preserved by pullback along a flat morphism

Let `g : V ⟶ W` be a flat morphism of algebraic spaces over an algebraic space `Z`, so that
`v = g ≫ w` for the structure morphisms `v : V ⟶ Z` and `w : W ⟶ Z`, and let `M` be a
quasi-coherent `𝒪_W`-module flat over `Z`.  Then `g^*M` is flat over `Z`.

This is the first assertion of Stacks 05VY at every point of `|V|`: flatness of `g` at a point
`x` makes `M` flat over `Z` at the image of `x` equivalent to `g^*M` flat over `Z` at `x`.

Flatness of `g` cannot be dropped: for the inclusion `g` of a closed point of `Z = 𝔸¹_k` and
`M = 𝒪_Z` (so `W = Z`, `w = 𝟙 Z`), the module `M` is flat over `Z` while `g^*M = 𝒪_g` is not.
So the statement `AlgebraicGeometry.Space.FlatOverPullbackOver` of
`StacksFrontier/AlgebraicGeometry/Quot/QuotientFunctorSourceSheaf.lean`, which asks this for an
arbitrary `g` and an arbitrary module, is false; the result below is the form its consumers
use, where `g` is a base change of a member of an fpqc covering, hence flat.

## Main results

* `AlgebraicGeometry.Space.isFlatOver_modulePullback_of_isFlat`: the pullback of a
  quasi-coherent module flat over `Z` along a flat morphism over `Z` is flat over `Z`.

## References

* [Stacks Project, Tag 05VY](https://stacks.math.columbia.edu/tag/05VY)
* [Stacks Project, Tag 05VV](https://stacks.math.columbia.edu/tag/05VV)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Relative flatness is preserved by pullback along a flat morphism.**  For a flat morphism
`g : V ⟶ W` of algebraic spaces over `Z` and a quasi-coherent `𝒪_W`-module `M` flat over `Z`,
the pullback `g^*M` is flat over `Z`.

Both sides are read pointwise, and at each point of `|V|` this is the pointwise equivalence of
Stacks 05VY for the flat morphism `g`. -/
theorem isFlatOver_modulePullback_of_isFlat {V W Z : AlgebraicSpaces B S hS} {w : W ⟶ Z}
    {v : V ⟶ Z} (g : V ⟶ W) (hg : IsFlat B S hS g.hom) (hgw : g ≫ w = v)
    (M : Modules.{u, u} B S hS W.1 W.2) (hM : M.IsQuasicoherentOnSite)
    (hflat : IsFlatOver B S hS W.2 w.hom M) :
    IsFlatOver B S hS V.2 v.hom ((modulePullback B S hS g).obj M) := by
  subst hgw
  have : M.IsQuasicoherentOnSite := hM
  refine (isFlatOver_iff_forall_isFlatOverAtPoint B S hS (g ≫ w) _
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS g M hM)).2
    fun x => ?_
  exact (isFlatOverAtPoint_modulePullback_iff_of_isFlatAt B S hS g w M x
    (isFlatAt_of_isFlat B S hS g.hom hg x)).1
    ((isFlatOver_iff_forall_isFlatOverAtPoint B S hS w M hM).1 hflat _)

end AlgebraicGeometry.Space

end
