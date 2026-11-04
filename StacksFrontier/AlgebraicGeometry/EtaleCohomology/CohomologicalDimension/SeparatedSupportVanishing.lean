module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.TrdegSupportVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.DerivedCategoryOfTorsionSheaves

/-!
# Vanishing for torsion sheaves supported in `E_a` on a separated scheme

Let `K` be a field and `X` a separated, quasi-compact scheme locally of finite type over `K`. Let
`c` be a bound for the étale cohomology of torsion abelian sheaves on every separated,
quasi-compact scheme of finite type over `K` of dimension at most `a`. If a torsion abelian sheaf
`𝓕` on `X_ét` has support in the set `E_a` of points `x` with `trdeg_K κ(x) ≤ a`, then
`H^b(X, 𝓕) = 0` for `b > c`.

This is the argument of Interlude II in the proof of Stacks 0F0V
(`AlgebraicGeometry.subsingleton_H_of_smallEtaleSupport_subset_of_cdBound`, for affine `X` and
the bound `a + cd(K)`), run with separated instead of affine schemes: `𝓕` is the filtered colimit
of subsheaves supported on closed subsets `W ⊆ E_a` (Stacks 0F0N), each of which is the direct
image of its restriction to the reduced closed subscheme on `W` (Stacks 04CA), a separated scheme
of finite type over `K` of dimension at most `a` (Stacks 0A21), and étale cohomology commutes with
filtered colimits on a quasi-compact quasi-separated scheme (Stacks 03Q5). The same argument with
the bound `2a` is the support form of `cd(X) ≤ 2 dim X` consumed by its induction.

## Main results

* `AlgebraicGeometry.subsingleton_H_of_smallEtaleSupport_subset_of_separatedBound`.

## References

* [Stacks Project, Tag 0F0V](https://stacks.math.columbia.edu/tag/0F0V)
* [Stacks Project, Tag 0F0N](https://stacks.math.columbia.edu/tag/0F0N)
* [Stacks Project, Tag 04CA](https://stacks.math.columbia.edu/tag/04CA)
* [Stacks Project, Tag 03Q5](https://stacks.math.columbia.edu/tag/03Q5)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

open Stacks.EtaleCohomology

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology
  Stacks.EtaleCohomology.smallEtaleGlobalSectionsAb_additive

/-- **Vanishing for torsion sheaves supported in `E_a`, on a separated scheme.** Let `K` be a
field, `X` separated, quasi-compact and locally of finite type over `K`, and `c` a bound for the
étale cohomology of torsion abelian sheaves on every separated, quasi-compact scheme `Z` locally
of finite type over `K` with `dim Z ≤ a` (`hV`). If `𝓕` is a torsion abelian sheaf on `X_ét`
whose support is contained in the set `E_a` of points `x` with `trdeg_K κ(x) ≤ a`, then
`H^b(X, 𝓕) = 0` for `b > c`. -/
theorem subsingleton_H_of_smallEtaleSupport_subset_of_separatedBound (K : Type u) [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] [IsSeparated f]
    [CompactSpace X] (a : ℕ) (c : ℕ∞)
    (hV : ∀ (Z : Scheme.{u}) (g : Z ⟶ Spec (.of K)) [LocallyOfFiniteType g] [IsSeparated g]
      [CompactSpace Z], topologicalKrullDim Z ≤ a → Scheme.IsEtaleCohomologyBound Z c)
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F)
    (hsupp : Stacks.EtaleCohomology.smallEtaleSupport F ⊆ Scheme.trdegLESet K f a)
    (b : ℕ) (hb : c < b) :
    Subsingleton (Sheaf.H.{u + 1, u + 1} F b) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian X := {}
  let E : Set X := Scheme.trdegLESet K f a
  have hE : StableUnderSpecialization E := Scheme.stableUnderSpecialization_trdegLESet K f a
  have hG := (smallEtaleSupport_subset_iff F E).1 hsupp
  obtain ⟨I, _, _, D, ι, ⟨hcolim⟩, hmonos, hD⟩ :=
    exists_isFilteredColimit_isClosed_support_smallEtale E hE F hG
  -- the cohomology of each term vanishes
  have hterm : ∀ i, IsZero (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerived
      b).obj (D.obj i)) := by
    intro i
    obtain ⟨W, hW, hWE, hWsupp⟩ := hD i
    have hmono : Mono (ι.app i) := hmonos i
    let J := Scheme.IdealSheafData.vanishingIdeal (⟨W, hW⟩ : TopologicalSpace.Closeds X)
    let i₀ : J.subscheme ⟶ X := J.subschemeι
    have hrange : Set.range i₀ = W := by
      rw [Scheme.IdealSheafData.range_subschemeι, Scheme.IdealSheafData.coe_support_vanishingIdeal]
      rfl
    have hunit := isIso_smallEtaleAdjunctionAb_unit_app_of_isZero_stalk i₀ (D.obj i)
      (fun s hs => hWsupp s (by rwa [hrange] at hs))
    let H := (smallEtalePullbackAb i₀).obj (D.obj i)
    have hDtors : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology (D.obj i) :=
      (Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology).prop_of_mono (ι.app i) hF
    have hH : Stacks.Torsion.torsionSheafProperty J.subscheme.smallEtaleTopology H :=
      Stacks.Torsion.torsionSheafProperty_of_iso _
        ((smallEtalePullbackAbIsoEtaleAbelianInverseImage i₀).app (D.obj i)).symm
        (torsionSheafProperty_etaleAbelianInverseImage.{u, u + 1} i₀ (D.obj i) hDtors)
    have : CompactSpace J.subscheme :=
      (IsClosedImmersion.isClosedEmbedding i₀).compactSpace
    -- the closed subscheme has dimension at most `a`
    have hdim : topologicalKrullDim J.subscheme ≤ a := by
      rw [topologicalKrullDim_eq_iSup_trdeg_residueField K J.subscheme (i₀ ≫ f)]
      refine iSup_le fun z => ?_
      have htr := trdeg_residueField_of_surjectiveOnStalks K f i₀ z.1
      have hz : i₀ z.1 ∈ E := hWE (hrange ▸ ⟨z.1, rfl⟩)
      simp only [E, Scheme.trdegLESet, Set.mem_ofPred_eq] at hz
      rw [htr] at hz
      exact_mod_cast Cardinal.toENat_le_natCast.2 hz
    have h1 : Subsingleton (Sheaf.H.{u + 1, u + 1} H b) :=
      hV J.subscheme (i₀ ≫ f) hdim H hH b hb
    have h2 : Subsingleton (Sheaf.H.{u + 1, u + 1} ((smallEtalePushforwardAb i₀).obj H) b) :=
      (Equiv.ofBijective _
        (etaleCohomologyDirectImageMap_bijective.{u, 0, u + 1} i₀ H b)).subsingleton_congr.2 h1
    have h3 := (Stacks.Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{0}
      _ _ _).1 h2
    exact h3.of_iso (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerived b).mapIso
      (asIso ((smallEtaleAdjunctionAb i₀).unit.app (D.obj i))))
  -- cohomology commutes with filtered colimits (Stacks 03Q5)
  have h03Q5 := Stacks.EtaleCohomology.isIso_colimit_post_rightDerived_Γ_smallEtale.{0, u} X b D
  have hzero : IsZero (colimit (D ⋙ (Sheaf.Γ X.smallEtaleTopology
      AddCommGrpCat.{u + 1}).rightDerived b)) := by
    refine (IsZero.iff_id_eq_zero _).2 (colimit.hom_ext fun i => ?_)
    exact (hterm i).eq_of_src _ _
  have hF' : IsZero (((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerived b).obj
      F) := by
    refine (hzero.of_iso (asIso (colimit.post D
      ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerived b))).symm).of_iso ?_
    exact ((Sheaf.Γ X.smallEtaleTopology AddCommGrpCat.{u + 1}).rightDerived b).mapIso
      (hcolim.coconePointUniqueUpToIso (colimit.isColimit D))
  exact (Stacks.Cohomology.GlobalSections.subsingleton_sheafH_iff_isZero_rightDerivedΓ.{0}
    _ _ _).2 hF'

end AlgebraicGeometry

end
