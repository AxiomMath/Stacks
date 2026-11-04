module

public import Mathlib.Algebra.Category.FGModuleCat.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Pullback
public import Mathlib.RingTheory.Noetherian.Basic
public import Mathlib.Topology.Constructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.Stratification
public import StacksFrontier.AlgebraicGeometry.Spaces.ProetaleComparison
public import StacksCore.Tactic.StacksAttribute

/-!
# Constructible sheaves of modules on the small pro-étale site

A sheaf of modules over a Noetherian ring on the small pro-étale site of a scheme is
*constructible* when every affine open admits a finite partition into constructible locally
closed subschemes on whose members the inverse image of the sheaf is locally constant of
finite type.

The partition is `AlgebraicGeometry.Scheme.ConstructibleStratification`; local constancy with
finitely generated local values is `Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant`.

## Main definitions

* `AlgebraicGeometry.ProEtale.IsConstructibleModuleSheaf`: constructibility of a sheaf of
  modules on the small pro-étale site.

## Main results

There are no theorems in this file; it supplies the definition above.

## Implementation notes

Local constancy of finite type is `Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant`, taken
here at the small pro-étale topology; it is the same predicate the étale theory of Tag 03RW
uses.

A stratum of a `ProEtale.ConstructibleStratification` is given by a morphism of schemes rather
than by a subset: the source's strata are locally closed *subschemes*, so each carries a scheme
structure and the restriction of a sheaf to it is inverse image along the stratum's inclusion.
Locally closedness is encoded as `IsImmersion` of that inclusion, and constructibility is asked
of the
stratum's image inside the ambient open, which is where the source asks for it. This is a
different object from the purely topological `FiniteStratification` of
`StacksFrontier.Topology.Stratification.RefineConstructible`, whose strata are subsets of a
topological space ordered so that closures are downward closed.

Restriction of a pro-étale sheaf to a stratum is inverse image along pro-étale base change
`AlgebraicGeometry.Scheme.proetaleBaseChange` of the stratum's inclusion, taken in Mathlib's
sheafified left-Kan-extension form. The instance hypotheses record what that inverse image
needs: sheafification on the small pro-étale site of every scheme and of its localizations, and
that pro-étale pushforward is a right adjoint, so that `sheafPullback` is its left adjoint.

## References

* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
* [Stacks Project, Tag 09AJ](https://stacks.math.columbia.edu/tag/09AJ)
* [Stacks Project, Tag 0A52](https://stacks.math.columbia.edu/tag/0A52)
-/

@[expose] public noncomputable section

open CategoryTheory

universe w v u r c

namespace AlgebraicGeometry

namespace ProEtale

/-- **Stacks 09AJ.** A sheaf of `Λ`-modules on the small pro-étale site of `X`, with `Λ`
Noetherian, is *constructible* if every affine open of `X` has a finite partition into
constructible locally closed subschemes on each of which the inverse image of the sheaf is
locally constant of finite type. -/
@[stacks 09AJ]
abbrev IsConstructibleModuleSheaf (X : Scheme.{u}) (Λ : Type v) [CommRing Λ]
    [IsNoetherianRing Λ]
    [∀ Y : Scheme.{u}, HasWeakSheafify (Scheme.ProEt.topology Y) (ModuleCat.{w} Λ)]
    [∀ (Y : Scheme.{u}) (V : Y.ProEt),
      HasWeakSheafify ((Scheme.ProEt.topology Y).over V) (ModuleCat.{w} Λ)]
    [∀ {Z Y : Scheme.{u}} (f : Z ⟶ Y),
      ((Scheme.proetaleBaseChange f).sheafPushforwardContinuous
        (ModuleCat.{w} Λ) (Scheme.ProEt.topology Y)
        (Scheme.ProEt.topology Z)).IsRightAdjoint]
    (F : Sheaf (Scheme.ProEt.topology X) (ModuleCat.{w} Λ)) : Prop :=
  ∀ U : X.affineOpens,
    ∃ s : Scheme.ConstructibleStratification X U.1,
      ∀ i, Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ
        (Scheme.ProEt.topology (s.piece i))
        (((Scheme.proetaleBaseChange (s.inclusion i)).sheafPullback
          (ModuleCat.{w} Λ) (Scheme.ProEt.topology X)
          (Scheme.ProEt.topology (s.piece i))).obj F)

end ProEtale

end AlgebraicGeometry

end
