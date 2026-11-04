module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleRankOne.SiteConverse
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierDivisor
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleLocallyRinged
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite

/-!
# An invertible module on an algebraic space is finite locally free of rank one, hence
quasi-coherent

Let `X` be an algebraic space over a scheme `S`.  An invertible `𝒪_X`-module on the small étale
site of `X` — invertible in the sense of Stacks 01CS, that tensoring by it is an autoequivalence
of `𝒪_X`-modules — is finite locally free of rank one, because the small étale site of an
algebraic space is locally ringed.  Being finite locally free it is of finite presentation, and
therefore quasi-coherent.

## Main results

* `AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_one_of_isInvertible`: an invertible
  `𝒪_X`-module is finite locally free of rank one.
* `AlgebraicGeometry.Space.isQuasicoherentOnSite_of_isInvertible`: an invertible `𝒪_X`-module is
  quasi-coherent.

## Implementation notes

Rank one is Stacks 0B8Q for the small étale site, read off from
`AlgebraicGeometry.RingedSite.isFiniteLocallyFreeOfRank_one_of_isInvertible'`: that result wants
the two sheafification hypotheses at `AddCommGrpCat.{u}`, the universe of the sections of `𝒪_X`,
and the site to be locally ringed, which is Stacks 04KH.  Its invertibility hypothesis is stated
with the class of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Invertible`, so it is fed through the comparison
`Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry` with the class of
`StacksFrontier.Topology.Sheaves.Modules.Invertible`, which is the one the divisor files use.

Quasi-coherence then goes through finite presentation rather than directly: a finite locally free
module on a site is of finite presentation, and a module of finite presentation is quasi-coherent,
both of which are instances of Stacks 03DL.
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- **Stacks 0B8Q on the small étale site of an algebraic space.**  An invertible `𝒪_X`-module
is finite locally free of rank one. -/
theorem isFiniteLocallyFreeOfRank_one_of_isInvertible
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X))
    (h : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property M) :
    RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2) M 1 := by
  have h₁ : HasWeakSheafify (smallEtaleRingedSite B S hS X.1 X.2).J AddCommGrpCat.{u} :=
    inferInstanceAs (HasWeakSheafify (SmallEtale.topology B S hS X.1) AddCommGrpCat.{u})
  have h₂ : (smallEtaleRingedSite B S hS X.1 X.2).J.WEqualsLocallyBijective AddCommGrpCat.{u} :=
    inferInstanceAs ((SmallEtale.topology B S hS X.1).WEqualsLocallyBijective AddCommGrpCat.{u})
  have h₃ : Stacks.SheafOfModules.IsInvertible
      (smallEtaleRingedSite B S hS X.1 X.2).O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).property M :=
    Stacks.SheafOfModules.IsInvertible.ofAlgebraicGeometry _ _ _ h
  exact RingedSite.isFiniteLocallyFreeOfRank_one_of_isInvertible'
    (smallEtaleRingedSite B S hS X.1 X.2) _
    (smallEtaleRingedSite_isLocallyRinged B S hS X.1 X.2)

/-- **An invertible `𝒪_X`-module on an algebraic space is quasi-coherent.**  It is finite
locally free of rank one, hence of finite presentation, hence quasi-coherent. -/
theorem isQuasicoherentOnSite_of_isInvertible
    (M : SheafOfModules.{u} (structureRingSheaf B S hS X))
    (h : AlgebraicGeometry.SheafOfModules.IsInvertible (structureCommRings B S hS X)
      (structureRingSheaf B S hS X).property M) :
    M.IsQuasicoherentOnSite := by
  have hfree : SheafOfModules.IsFiniteLocallyFreeOnSite M :=
    (isFiniteLocallyFreeOfRank_one_of_isInvertible B S hS X M h).isFiniteLocallyFreeOnSite
  have : M.IsFinitePresentationOnSite :=
    SheafOfModules.isFinitePresentationOnSite_of_isFiniteLocallyFreeOnSite hfree
  infer_instance

end AlgebraicGeometry.Space

end
