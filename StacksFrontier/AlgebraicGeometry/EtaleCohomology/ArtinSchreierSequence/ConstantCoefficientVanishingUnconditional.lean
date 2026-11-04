module
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ConstantSequenceDatum
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.FlasqueCechVanishing
public import StacksFrontier.Topology.Sheaves.Cohomology.CompactSubset.RestrictionUnivLE
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ConstantCoefficientVanishing
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ConstantCoefficientVanishing

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.AlgebraicGeometry.Sites.AffineEtale
public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.Data.ZMod.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.AdditiveSheafCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ConstantKernel
public import StacksFrontier.AlgebraicGeometry.Properties.Constructible
public import StacksFrontier.RingTheory.LocalCohomology.Deps.QuasicoherentAffineVanishing
public import StacksFrontier.RingTheory.LocalCohomology.DimensionVanishing.HgroupOfSheafCohomology
public import StacksFrontier.Topology.Sheaves.Cohomology.Vanishing.SpectralSpaces

/-!
# Vanishing of the étale cohomology of `𝐙/p𝐙` above the dimension

Let `p` be a prime and let `S` be a quasi-compact and quasi-separated scheme of characteristic
`p` whose underlying space has Krull dimension at most `d`. Then `H ^ q (S_étale, 𝐙/p𝐙) = 0` for
every `q ≥ d + 2`, with `Ext` groups in an arbitrary universe.

## Main results

* `Stacks.ArtinSchreier.subsingleton_etaleH_constantZMod_of_topologicalKrullDim_le_unconditional`:
  [Stacks, Tag 0A3K] (2).
-/
@[expose] public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

universe w w₁ v₁ u₁ u

namespace Stacks.ArtinSchreier

/-- Let `p` be a prime and let `S` be a quasi-compact and quasi-separated scheme of
characteristic `p` and of dimension at most `d`. Then `H ^ q (S_étale, 𝐙/p𝐙) = 0` for every
`q ≥ d + 2`. Only the upper bound on the dimension of `S` is needed. -/
@[stacks 0A3K "(2)"]
public theorem subsingleton_etaleH_constantZMod_of_topologicalKrullDim_le_unconditional (p : ℕ)
    [Fact p.Prime] (S : Scheme.{u}) [CompactSpace S] [QuasiSeparatedSpace S]
    (hS : (p : Γ(S, ⊤)) = 0)
    [HasExt.{w} (Sheaf S.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (d : ℕ) (hdim : topologicalKrullDim (S : Type u) ≤ (d : WithBot ℕ∞))
    (q : ℕ) (hq : d + 2 ≤ q) :
    Subsingleton (Sheaf.H.{w, u + 1} (etaleConstantZMod S p) q) :=
  let : HasExt.{u} (Sheaf (Opens.grothendieckTopology (S : Type u)) AddCommGrpCat.{u}) :=
    Stacks.Topology.hasExt_sheafOpens.{u, u} S.toTopCat
  _root_.Stacks.ArtinSchreier.subsingleton_etaleH_constantZMod_of_hgroup_vanishing_constantSequence
    p S hS d
    (fun i hi => Stacks.LocalCohomology.isZero_Hgroup_of_subsingleton_sheafCohomology
      (SheafOfModules.unit S.ringCatSheaf) i (by omega)
      (Stacks.CohomologyVanishing.subsingleton_sheafH_of_topologicalKrullDim_le d (S : Type u)
        inferInstance inferInstance
        ((SheafOfModules.toSheaf S.ringCatSheaf).obj (SheafOfModules.unit S.ringCatSheaf))
        i hdim hi))
    q hq

end Stacks.ArtinSchreier

end
