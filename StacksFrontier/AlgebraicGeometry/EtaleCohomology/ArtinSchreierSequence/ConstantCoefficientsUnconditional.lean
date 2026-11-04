module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.GaCohomologyAddEquiv
public import StacksFrontier.AlgebraicGeometry.TopDegreeCoherentFiniteness.Full
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ProperConstantCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ConstantSequenceDatum

/-!
# Cohomology of `𝐙/p𝐙` in characteristic `p`

Let `X` be a scheme over an algebraically closed field `k` of characteristic `p > 0`. The étale
cohomology of `𝐙/p𝐙` on `X` is computed from the Artin–Schreier sequence
`Stacks.ArtinSchreier.constantArtinSchreierSequenceDatum` ([Stacks, Tag 0A3J]) and the comparison
`Stacks.ArtinSchreier.gaFrobeniusComparison` of the étale cohomology of `𝐆_a` with the cohomology
of the structure sheaf. For `X` proper over `k` the groups `H ^ q (X_étale, 𝐙/p𝐙)` are finite;
for `X` separated and of finite type over `k` of dimension `d`, with `H ^ d (X, 𝒪_X)`
finite-dimensional, they vanish for `q ≥ d + 1`.

All statements are for an arbitrary `Ext` universe `w`.

## Main definitions

* `Stacks.ArtinSchreier.sheafHChgUniv`: sheaf cohomology does not depend on the universe of its
  `Ext` groups.

## Main results

* `Stacks.ArtinSchreier.finite_etaleH_constantZMod_of_isProper'`: [Stacks, Tag 0A3P] (1).
* `Stacks.ArtinSchreier.subsingleton_etaleH_constantZMod_of_finiteDimensional`:
  [Stacks, Tag 0A3N], with the finite dimensionality of `H ^ d (X, 𝒪_X)` as a hypothesis; it
  holds by [Stacks, Tag 0A3M],
  `AlgebraicGeometry.finiteDimensional_cohomologyOverField_topologicalKrullDim`.

## References

* [Stacks Project, Tag 0A3N](https://stacks.math.columbia.edu/tag/0A3N)
* [Stacks Project, Tag 0A3P](https://stacks.math.columbia.edu/tag/0A3P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

universe w u

namespace Stacks.ArtinSchreier

attribute [local instance] Stacks.Topology.hasExt_sheafOpens

/-- `Ext` of abelian sheaves at the object universe of the small étale site. -/
local instance (priority := high) hasExt_smallEtale_succ' (X : Scheme.{u}) :
    HasExt.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
  haveI : IsGrothendieckAbelian.{u + 1} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}) :=
    Stacks.EtaleCohomology.isGrothendieckAbelian_sheaf_smallEtale_objectUniverse X
  CategoryTheory.IsGrothendieckAbelian.hasExt _

/-- Sheaf cohomology does not depend on the universe of its `Ext` groups, up to equivalence. -/
def sheafHChgUniv {C : Type*} [Category* C] {J : GrothendieckTopology C}
    [HasSheafify J AddCommGrpCat.{u + 1}] [HasExt.{w} (Sheaf J AddCommGrpCat.{u + 1})]
    [HasExt.{u + 1} (Sheaf J AddCommGrpCat.{u + 1})] (F : Sheaf J AddCommGrpCat.{u + 1}) (q : ℕ) :
    Sheaf.H.{w} F q ≃ Sheaf.H.{u + 1} F q :=
  Ext.chgUniv

/-- Let `X` be a scheme proper over an algebraically closed field `k` of characteristic `p > 0`.
Then `H ^ q (X_étale, 𝐙/p𝐙)` is finite for every `q`. -/
@[stacks 0A3P "part (1)"]
theorem finite_etaleH_constantZMod_of_isProper' {p : ℕ} (hp : 0 < p) (k : Type u) [Field k]
    [IsAlgClosed k] [CharP k p] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [IsProper f]
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})] (q : ℕ) :
    Finite (Sheaf.H.{w, u + 1} (etaleConstantZMod X p) q) := by
  have hpp : p.Prime := CharP.char_prime_of_ne_zero k hp.ne'
  have : Finite (Sheaf.H.{u + 1, u + 1} (etaleConstantZMod X p) q) :=
    finite_etaleH_constantZMod_of_isProper.{u + 1} k f
      (constantArtinSchreierSequenceDatum X hpp (natCast_eq_zero_of_charP k p f)) q hp
      (fun i => gaFrobeniusComparison k f hpp i)
  exact Finite.of_equiv _ (sheafHChgUniv _ q).symm

/-- Let `X` be separated and of finite type over an algebraically closed field `k` of
characteristic `p > 0`, of dimension `d`, with `H ^ d (X, 𝒪_X)` finite-dimensional. Then
`H ^ q (X_étale, 𝐙/p𝐙) = 0` for every `q ≥ d + 1`. This is [Stacks, Tag 0A3N] with the finite
dimensionality of [Stacks, Tag 0A3M] as a hypothesis. -/
theorem subsingleton_etaleH_constantZMod_of_finiteDimensional {p : ℕ} (hp : 0 < p) (k : Type u)
    [Field k] [IsAlgClosed k] [CharP k p] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (d : ℕ) (hd : topologicalKrullDim (X : Type u) = (d : WithBot ℕ∞))
    (hfin : FiniteDimensional k
      (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) d))
    (q : ℕ) (hq : d + 1 ≤ q) :
    Subsingleton (Sheaf.H.{w, u + 1} (etaleConstantZMod X p) q) := by
  have hpp : p.Prime := CharP.char_prime_of_ne_zero k hp.ne'
  have : Subsingleton (Sheaf.H.{u + 1, u + 1} (etaleConstantZMod X p) q) :=
    subsingleton_etaleH_constantZMod_of_isAlgClosed.{u + 1} hp k f
      (constantArtinSchreierSequenceDatum X hpp (natCast_eq_zero_of_charP k p f))
      (fun i h => subsingleton_sheafH_additiveSheaf_of_isZero_hgroup_allDegrees i h) d hd
      (gaFrobeniusComparison k f hpp d) hfin q hq
  exact (sheafHChgUniv _ q).subsingleton

end Stacks.ArtinSchreier

end
