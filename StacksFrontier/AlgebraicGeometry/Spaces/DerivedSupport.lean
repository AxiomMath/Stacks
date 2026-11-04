module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafSupport
import StacksCore.Tactic.StacksAttribute

/-!
# Derived objects supported on a subset of an algebraic space

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`, and let `E`
be an object of the derived category `D(𝒪_F)` of `𝒪_F`-modules, that is, of sheaves of modules
on the small étale ringed site `AlgebraicGeometry.Space.smallEtaleRingedSite` of `F`.  Then `E`
is *supported on* a subset `T ⊆ |F|` when every cohomology sheaf `Hⁱ(E)` is supported on `T`,
the support of a sheaf on the small étale site being `AlgebraicGeometry.Space.supportOfSheaf`
of Stacks 04KA.

## Main definitions

* `AlgebraicGeometry.Space.CohomologySupportedOn` is that condition.

## Main results

* `AlgebraicGeometry.Space.CohomologySupportedOn.mono` is monotonicity in the subset.

## Implementation notes

Support of a cohomology sheaf is taken on the underlying sheaf of abelian groups, which is
what `AlgebraicGeometry.Space.supportOfSheaf` consumes; `SheafOfModules.toSheaf` performs that
forgetting.  Consequently the universe of the module sections stays independent of the universe
of the schemes, exactly as for `AlgebraicGeometry.Space.Modules` and
`AlgebraicGeometry.Space.QuasicoherentDerivedCategory`, and the two sheafification hypotheses
are the ones under which Mathlib equips the `𝒪_F`-modules at that universe with their abelian
structure and hence with a derived category.  They are hypotheses rather than instances for the
same reason as in `AlgebraicGeometry.Space.QuasicoherentDerivedCategory`: at the module universe
`u` of the structure rings they are available from
`AlgebraicGeometry.Space.ModulesAbelian`, but the definition is stated at a free module
universe.

The source states the condition for a *closed* subset `T ⊆ |F|`; it is stated here for an
arbitrary subset, which is the source's notion when `T` is closed and which also applies
directly to inverse images of closed subsets along a morphism — the form in which the
induction principle of the chapter uses it.  Nothing is lost: the supports themselves are
closed where that is known, by `AlgebraicGeometry.Space.isClosed_supportOfSection`.

The condition is stated through the support of the cohomology sheaves rather than stalkwise,
which is how the analogue `AlgebraicGeometry.CohomologySupportedOn` for a ringed topological
space is phrased.  On the small étale site the stalkwise form would have to choose a geometric
point over each point of `|F|`, and the independence of that choice is not available: it needs
the comparison of étale local rings at two geometric points over one point (Stacks 04K0), which
`AlgebraicGeometry.Space.supportOfSheaf` avoids by quantifying existentially over the geometric
points.

## References

* [Stacks Project, Tag 08GF](https://stacks.math.columbia.edu/tag/08GF)
* [Stacks Project, Tag 04KA](https://stacks.math.columbia.edu/tag/04KA)
-/

@[expose] public section

open CategoryTheory

universe u m

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **Stacks 08GF.** An object `E` of `D(𝒪_F)` is *supported on* a subset `T` of `|F|` when
every one of its cohomology sheaves `Hⁱ(E)` is supported on `T`. -/
@[stacks 08GF]
noncomputable abbrev CohomologySupportedOn
    [HasSheafify (smallEtaleRingedSite B S hS F hF).J AddCommGrpCat.{m}]
    [(smallEtaleRingedSite B S hS F hF).J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    (T : Set (points B S hS F))
    (E : DerivedCategory (Modules.{u, m} B S hS F hF)) : Prop :=
  ∀ i : ℤ,
    supportOfSheaf B S hS F
      ((SheafOfModules.toSheaf
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).obj
        ((DerivedCategory.homologyFunctor (Modules.{u, m} B S hS F hF) i).obj E)) ⊆ T

/-- An object supported on a subset is supported on any larger subset. -/
theorem CohomologySupportedOn.mono
    [HasSheafify (smallEtaleRingedSite B S hS F hF).J AddCommGrpCat.{m}]
    [(smallEtaleRingedSite B S hS F hF).J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    {T T' : Set (points B S hS F)} {E : DerivedCategory (Modules.{u, m} B S hS F hF)}
    (hE : CohomologySupportedOn B S hS F hF T E) (hT : T ⊆ T') :
    CohomologySupportedOn B S hS F hF T' E :=
  fun i ↦ (hE i).trans hT

end AlgebraicGeometry.Space

end
