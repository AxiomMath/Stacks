module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantWeakSerre
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyConstantWeakSerreSupplement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeContinuous
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.Stratification
public import StacksFrontier.AlgebraicGeometry.ProEtale.Constructible.StratificationSupplement

/-!
# Constructible sheaves of modules on the small étale site

Let `Λ` be a Noetherian ring and `X` a scheme. A sheaf of `Λ`-modules on the small étale site
`X_étale` is *constructible* when every affine open `U` of `X` admits a finite decomposition
`U = ∐ Uᵢ` into constructible locally closed subschemes such that the inverse image of the sheaf
to each `Uᵢ` is locally constant of finite type.

## Main definitions

* `AlgebraicGeometry.Scheme.IsConstructibleEtaleModuleSheaf`: constructibility of a sheaf of
  `Λ`-modules on Mathlib's small étale site `AlgebraicGeometry.Scheme.smallEtaleTopology`.

## Implementation notes

The decompositions are the site-free `AlgebraicGeometry.Scheme.ConstructibleStratification`, the
same ones that constructibility on the small pro-étale site
(`AlgebraicGeometry.ProEtale.IsConstructibleModuleSheaf'`) quantifies over, so that the two
notions can be compared stratum by stratum. Restriction to a stratum is inverse image along
small étale base change `Stacks.EtaleCohomology.smallEtaleBaseChange`, as a sheafified left Kan
extension. Locally constant of finite type is
`Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf`. The sections live in the universe
`max (u + 1) v w`, which contains the site and the coefficients; there sheafification and the
left Kan extensions exist unconditionally, so the definition carries no instance hypotheses.

`AlgebraicGeometry.IsConstructibleModuleSheaf` states the same condition on the small étale site
cut out of a chosen big étale site.

## References

* [Stacks Project, Tag 03RW](https://stacks.math.columbia.edu/tag/03RW)
* [Stacks Project, Tag 05BE](https://stacks.math.columbia.edu/tag/05BE)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v w

namespace AlgebraicGeometry.Scheme

/-- A sheaf of `Λ`-modules on the small étale site of `X`, with `Λ` Noetherian, is
*constructible* if every affine open `U` of `X` has a finite partition into constructible locally
closed subschemes on each of which the inverse image of the sheaf is locally constant of finite
type. -/
abbrev IsConstructibleEtaleModuleSheaf (X : Scheme.{u}) (Λ : Type v) [CommRing Λ]
    [IsNoetherianRing Λ] (F : Sheaf X.smallEtaleTopology (ModuleCat.{max (u + 1) v w} Λ)) :
    Prop :=
  ∀ U : X.affineOpens, ∃ s : ConstructibleStratification X U.1, ∀ i,
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, max v w, v}
      (s.piece i).smallEtaleTopology Λ
      ((Functor.sheafPullbackConstruction.sheafPullback
        (Stacks.EtaleCohomology.smallEtaleBaseChange (s.inclusion i))
        (ModuleCat.{max (u + 1) v w} Λ) X.smallEtaleTopology (s.piece i).smallEtaleTopology).obj F)

/-- Constructibility of an étale sheaf of modules is invariant under isomorphism. -/
instance isClosedUnderIsomorphisms_isConstructibleEtaleModuleSheaf (X : Scheme.{u})
    (Λ : Type v) [CommRing Λ] [IsNoetherianRing Λ] :
    ObjectProperty.IsClosedUnderIsomorphisms (IsConstructibleEtaleModuleSheaf.{u, v, w} X Λ) where
  of_iso e hF U := by
    obtain ⟨s, hs⟩ := hF U
    exact ⟨s, fun i ↦ ObjectProperty.prop_of_iso _ (Functor.mapIso _ e) (hs i)⟩

end AlgebraicGeometry.Scheme

end
