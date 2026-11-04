module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.FrobeniusComparison
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ProperConstantCoefficients

/-!
# Finiteness of the cohomology of `𝐙/p𝐙` on a proper scheme in characteristic `p`

Let `X` be a proper scheme over an algebraically closed field `k` of characteristic `p > 0`.
[Stacks, Tag 0A3P] (1): every `H ^ q (X_étale, 𝐙/p𝐙)` is finite. Moreover `H ^ q (X_étale, 𝐙/p𝐙)`
vanishes for `q` above the dimension of `X`.

## Main results

* `Stacks.ArtinSchreier.finite_etaleH_constantZMod_of_isProper_of_isAlgClosed`: finiteness of
  `H ^ q (X_étale, 𝐙/p𝐙)`.
* `Stacks.ArtinSchreier.subsingleton_etaleH_constantZMod_of_isProper_of_isAlgClosed`: vanishing of
  `H ^ q (X_étale, 𝐙/p𝐙)` for `q ≥ dim X + 1`.

## References

* [Stacks Project, Tag 0A3P](https://stacks.math.columbia.edu/tag/0A3P)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Abelian AlgebraicGeometry TopologicalSpace

universe w u

namespace Stacks.ArtinSchreier

/-- **[Stacks, Tag 0A3P] (1).** Let `X` be a proper scheme over an algebraically closed field `k`
of characteristic `p > 0`. Then `H ^ q (X_étale, 𝐙/p𝐙)` is finite for every `q`. -/
@[stacks 0A3P "part (1)"]
theorem finite_etaleH_constantZMod_of_isProper_of_isAlgClosed {p : ℕ} (hp : p.Prime)
    (k : Type u) [Field k] [IsAlgClosed k] [CharP k p] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f]
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})] (q : ℕ) :
    Finite (Sheaf.H.{w, u + 1} (etaleConstantZMod X p) q) :=
  finite_etaleH_constantZMod_of_isProper k f
    (constantArtinSchreierSequenceDatum X hp (natCast_eq_zero_of_charP k p f)) q hp.pos
    (constantSequenceFrobeniusComparison hp k f)

attribute [local instance] Stacks.Topology.hasExt_sheafOpens in
/-- **Vanishing above the dimension for a proper scheme in characteristic `p`.** Let `X` be proper
over an algebraically closed field `k` of characteristic `p > 0`, of dimension `d`. Then
`H ^ q (X_étale, 𝐙/p𝐙) = 0` for every `q ≥ d + 1`.

This is the case of [Stacks, Tag 0A3N] where the finite dimensionality of `H ^ d (X, 𝒪_X)`
([Stacks, Tag 0A3M]) is supplied by properness. -/
theorem subsingleton_etaleH_constantZMod_of_isProper_of_isAlgClosed {p : ℕ} (hp : p.Prime)
    (k : Type u) [Field k] [IsAlgClosed k] [CharP k p] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsProper f]
    [HasExt.{w} (Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})]
    (d : ℕ) (hd : topologicalKrullDim (X : Type u) = (d : WithBot ℕ∞)) (q : ℕ) (hq : d + 1 ≤ q) :
    Subsingleton (Sheaf.H.{w, u + 1} (etaleConstantZMod X p) q) := by
  have : Fact p.Prime := ⟨hp⟩
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace X := (quasiCompact_iff_compactSpace f).mp inferInstance
  have : X.IsSeparated :=
    ⟨by simpa using (inferInstance : IsSeparated (f ≫ Limits.terminal.from (Spec (.of k))))⟩
  have : QuasiSeparatedSpace (X : Type u) := inferInstance
  have hS := natCast_eq_zero_of_charP k p f
  rcases Nat.lt_or_ge q (d + 2) with hq₂ | hq₂
  · obtain rfl : q = d + 1 := by lia
    refine subsingleton_sheafH_X₁_of_shortExact_of_surjective
      (constantArtinSchreierSequenceDatum X hp hS).shortExact d (d + 1) rfl
      (surjective_sheafH_map_of_topDegreeFrobeniusComparison hp.pos k f
        (constantArtinSchreierSequenceDatum X hp hS).φ
        (constantSequenceFrobeniusComparison hp k f d)
        (finiteDimensional_cohomologyOverField_of_isProper k f
          (SheafOfModules.unit X.ringCatSheaf) d))
      (subsingleton_sheafH_additiveSheaf_of_isZero_hgroup X (d + 1) (by lia) ?_)
    exact Stacks.LocalCohomology.isZero_Hgroup_of_subsingleton_sheafCohomology
      (SheafOfModules.unit X.ringCatSheaf) (d + 1) (by lia)
      (Stacks.CohomologyVanishing.subsingleton_sheafH_of_topologicalKrullDim_le d (X : Type u)
        inferInstance inferInstance
        ((SheafOfModules.toSheaf X.ringCatSheaf).obj (SheafOfModules.unit X.ringCatSheaf))
        (d + 1) hd.le (by lia))
  · exact subsingleton_etaleH_constantZMod_of_topologicalKrullDim_le_constantSequence p X hS d
      hd.le q hq₂

end Stacks.ArtinSchreier

end
