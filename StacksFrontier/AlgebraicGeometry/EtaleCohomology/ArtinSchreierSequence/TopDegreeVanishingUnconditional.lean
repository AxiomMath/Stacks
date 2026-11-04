module
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingExtensionGeneral
public import StacksFrontier.AlgebraicGeometry.AffineVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ConstantKernel
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.CohomologyComparison
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModuleFunctors
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.TopDegreeVanishing
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.TopDegreeVanishing

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ConstantCoefficientVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ConstantCoefficientVanishingUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.FrobeniusComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.FrobeniusComparisonUnconditional
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.FrobeniusSurjectivity
public import StacksFrontier.AlgebraicGeometry.TopDegreeCoherentFiniteness.SeparatedFiniteType
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.Cohomology

/-!
# Vanishing of étale cohomology of `𝐙/p𝐙` above the dimension

Let `X` be separated and of finite type over an algebraically closed field `k` of characteristic
`p > 0`. If `dim X ≤ d`, then `H ^ q (X_étale, 𝐙/p𝐙) = 0` for every `q ≥ d + 1`.

## Main results

* `Stacks.ArtinSchreier.subsingleton_etaleH_constantZMod_of_isAlgClosed_unconditional`:
  `H ^ q (X_étale, 𝐙/p𝐙)` is trivial for `q ≥ d + 1` whenever `dim X ≤ d`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian CategoryTheory.Limits Opposite TopologicalSpace
open AlgebraicGeometry

universe w w₁ v₁ u₁ u

namespace Stacks.ArtinSchreier

/-- Let `X` be separated and of finite type over an algebraically closed field `k` of
characteristic `p > 0`, and let `d` be a natural number with `dim X ≤ d`. Then
`H ^ q (X_étale, 𝐙/p𝐙) = 0` for every `q ≥ d + 1`. -/
@[stacks 0A3N, sga "4½ Arcata 4.4" "special case"]
public theorem subsingleton_etaleH_constantZMod_of_isAlgClosed_unconditional {p : ℕ} (hp : 0 < p)
    (k : Type u) [Field k] [IsAlgClosed k] [CharP k p] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (d : ℕ) (hd : topologicalKrullDim (X : Type u) ≤ (d : WithBot ℕ∞))
    (q : ℕ) (hq : d + 1 ≤ q) :
    Subsingleton (Sheaf.H.{w, u + 1} (etaleConstantZMod X p) q) := by
  have : NeZero p := ⟨Nat.ne_of_gt hp⟩
  have : Fact p.Prime := CharP.char_is_prime_of_pos k p
  have hpp : p.Prime := Fact.out
  have hX : (p : Γ(X, ⊤)) = 0 := by
    rw [← map_natCast ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom p, CharP.cast_eq_zero,
      map_zero]
  have : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  have : X.IsSeparated := by
    refine ⟨?_⟩
    have : IsSeparated (f ≫ terminal.from (Spec (.of k))) := inferInstance
    simpa using this
  have : QuasiSeparatedSpace (X : Type u) := inferInstance
  rcases Nat.lt_or_ge q (d + 2) with hq₂ | hq₂
  · obtain rfl : q = d + 1 := by omega
    have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    have hO : (SheafOfModules.unit X.ringCatSheaf).IsCoherent :=
      Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent X
    refine subsingleton_sheafH_X₁_of_shortExact_of_surjective
      (constantArtinSchreierSequence_shortExact.{u, 0} X hpp hX) d (d + 1) rfl
      (surjective_sheafH_map_artinSchreierMap.{u, 0} hpp k f hX d
        (finiteDimensional_cohomologyOverField_of_topologicalKrullDim_le k d f inferInstance
          inferInstance inferInstance hd _ hO))
      (subsingleton_sheafH_additiveSheaf_of_isZero_hgroup_unconditional.{w, 0} X (d + 1) (by omega)
        ?_)
    exact (isZero_cohomologyOverField_iff_isZero_hgroup k f _ (d + 1)).mp
      (_root_.AlgebraicGeometry.isZero_cohomologyOverField_of_topologicalKrullDim_le' k f _ hd
        (by omega))
  · exact subsingleton_etaleH_constantZMod_of_topologicalKrullDim_le_unconditional p X hX d hd q hq₂

end Stacks.ArtinSchreier

end
