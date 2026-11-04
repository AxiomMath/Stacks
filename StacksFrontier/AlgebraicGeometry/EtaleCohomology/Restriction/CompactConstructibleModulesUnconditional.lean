module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.CompactConstructibleModulesViaShriekPresentation
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.SmallEtaleModuleSheafInstances
import StacksCore.Tactic.StacksAttribute

/-!
# Constructible sheaves of modules on the small étale site are compact, with nothing assumed

Let `X` be a quasi-compact and quasi-separated scheme and `Λ` a Noetherian ring. Morphisms out of a
constructible sheaf of `Λ`-modules on `X_étale` commute with filtered colimits: for a filtered
colimit `G = colim G_i` of sheaves of `Λ`-modules, `Mor(F, G) = colim Mor(F, G_i)`. This is the
sheaves-of-modules case of Stacks 09Z4.

`AlgebraicGeometry.IsConstructibleModuleSheaf.isFinitelyPresentable` proves it for every pair of
arguments making the inverse image along small étale base change and the sheafification of module
presheaves on the slices exist — the two existence statements already needed to *state*
constructibility of a sheaf of `Λ`-modules, since
`AlgebraicGeometry.IsConstructibleModuleSheaf` is phrased through `f⁻¹` and through local
constancy on a slice. This file states the same conclusion with no such argument: for module
sections in `Type (u + 1)` and schemes in `Type u` both are theorems, at an arbitrary ring and
with no smallness or universe side condition left over, by
`AlgebraicGeometry.smallEtaleBaseChange_isRightAdjoint_sheafPushforward_moduleCat` and
`AlgebraicGeometry.SmallEtale.hasSheafify_over_moduleCat_of_univLE`, which instance search
supplies here.

Those two come from essential smallness of the small étale category
(`AlgebraicGeometry.SmallEtale.essentiallySmall_of_univLE`): sheafification is transported from a
small model, and the inverse image is the sheafified pointwise left Kan extension along the base
change functor.

## Main results

* `AlgebraicGeometry.IsConstructibleModuleSheaf.isFinitelyPresentable_unconditional` — **the
  sheaves-of-modules case of Stacks 09Z4** over an arbitrary Noetherian ring, with nothing
  assumed.

## Implementation notes

Compactness is `CategoryTheory.IsFinitelyPresentable`, which says that the covariant Hom functor
preserves filtered colimits; that is exactly the assertion that the canonical map
`colim Mor(F, G_i) → Mor(F, colim G_i)` is a bijection.

The coefficient universes are those forced by part (4) of Stacks 0738 on this site: the small
étale site of `B : BigEtaleSite.{u}` is a `Type (u + 1)` with `Category.{u}`, so the ring and the
module both live in `Type (u + 1)`. The universe inequality the two existence theorems ask for,
`UnivLE.{u, u + 1}`, is discharged by instance search from `UnivLE.self` and
`CategoryTheory.univLE_of_max`.

`X` is quasi-compact and quasi-separated, not Noetherian; the Noetherian hypothesis is on the
ring, where `AlgebraicGeometry.IsConstructibleModuleSheaf` carries it.

## References

* [Stacks Project, Tag 09Z4](https://stacks.math.columbia.edu/tag/09Z4)
* [Stacks Project, Tag 095N](https://stacks.math.columbia.edu/tag/095N)
* [Stacks Project, Tag 0738](https://stacks.math.columbia.edu/tag/0738)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- **The sheaves-of-`Λ`-modules case of Stacks 09Z4, with nothing assumed.** Let `X` be a
quasi-compact and quasi-separated scheme, let `Λ` be a Noetherian ring and let `F` be a
constructible sheaf of `Λ`-modules on `X_étale`. Then morphisms out of `F` commute with filtered
colimits of sheaves of `Λ`-modules: `Mor(F, colim G_i) = colim Mor(F, G_i)`.

The inverse image along small étale base change and the sheafification of presheaves of
`Λ`-modules on the slices of the small étale sites, through which constructibility of a sheaf of
`Λ`-modules is stated, are found here by instance search rather than taken as arguments. -/
@[stacks 09Z4 "sheaves of Λ-modules over an arbitrary Noetherian ring, with the inverse image \
along small étale base change and the sheafification on the slices proved rather than assumed"]
public theorem IsConstructibleModuleSheaf.isFinitelyPresentable_unconditional
    (B : BigEtaleSite.{u}) (X : B.Scheme) (R : Type (u + 1)) [CommRing R] [IsNoetherianRing R]
    [CompactSpace X.1] [QuasiSeparatedSpace X.1]
    (F : Sheaf (SmallEtale.topology B X.1 X.property) (ModuleCat.{u + 1} R))
    (hF : IsConstructibleModuleSheaf B X R F) :
    IsFinitelyPresentable.{u + 1} F :=
  IsConstructibleModuleSheaf.isFinitelyPresentable B X R F hF

end AlgebraicGeometry

end
