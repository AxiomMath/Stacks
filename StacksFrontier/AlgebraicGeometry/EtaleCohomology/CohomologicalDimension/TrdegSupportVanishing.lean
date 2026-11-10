module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.SupportedSheaves
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FilteredColimitsOfEtaleCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ModelBridges.ClosedSupportColimit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstantSheafVanishingTransport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionSheavesCurves.DirectImageCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleSupport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionInverseImage
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.SpecializationTrdeg
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Trdeg

/-!
# Cohomology of sheaves supported in bounded transcendence degree, given Stacks 0F0V

Let `K` be a field, `X` an affine scheme of finite type over `K`, and `E_a ⊆ X` the set of points
whose residue field has transcendence degree at most `a` over `K`. If every affine scheme of
finite type over `K` of dimension at most `a` has cohomological dimension at most `a + cd(K)`
(that is, if Stacks 0F0V holds in dimensions at most `a`), then every torsion abelian sheaf `𝓕` on
`X_ét` whose support is contained in `E_a` has `H^b(X, 𝓕) = 0` for `b > a + cd(K)`.

This is the proof of Stacks 0F0W, with the use of Stacks 0F0V isolated in the hypothesis `hV`, and
it is Interlude II of the proof of Stacks 0F0V, which uses it with the induction hypothesis as
`hV`. The unconditional Stacks 0F0W, with `hV` discharged by Stacks 0F0V, is
`AlgebraicGeometry.subsingleton_H_of_smallEtaleSupport_subset_trdegLESet`.

The proof is the source's. The set `E_a` is stable under specialization (Stacks 0A21), so `𝓕` is
a filtered colimit of subsheaves `𝓕ᵢ`, each supported on a closed subset `Wᵢ ⊆ E_a` (Stacks 0F0N,
`AlgebraicGeometry.exists_isFilteredColimit_isClosed_support_smallEtale`). On the reduced closed
subscheme `Zᵢ` with underlying set `Wᵢ`, which is affine of finite type over `K` and has dimension
at most `a` (Stacks 0A21), `𝓕ᵢ` is the direct image of its inverse image (Stacks 04CA), which is
torsion, so `H^b(X, 𝓕ᵢ) = H^b(Zᵢ, -)` (the direct image along a closed immersion being exact)
vanishes by `hV`. Cohomology commutes with filtered colimits on the quasi-compact and
quasi-separated scheme `X` (Stacks 03Q5, the form of Stacks 09YQ for a constant system of schemes).

## Main definitions

* `AlgebraicGeometry.Scheme.trdegLESet` — the set `E_a` of points of a scheme over a field `K`
  whose residue field has transcendence degree at most `a` over `K`.

## Main results

* `AlgebraicGeometry.Scheme.stableUnderSpecialization_trdegLESet` — `E_a` is stable under
  specialization.
* `AlgebraicGeometry.subsingleton_H_of_smallEtaleSupport_subset_of_cdBound` — Stacks 0F0W given
  Stacks 0F0V in dimensions at most `a`.

## References

* [Stacks Project, Tag 0F0W](https://stacks.math.columbia.edu/tag/0F0W)
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

/-- The set `E_a` of points `x` of a scheme `X` over a field `K` whose residue field has
transcendence degree at most `a` over `K`, the residue field being a `K`-algebra through global
sections and evaluation at `x`. -/
def Scheme.trdegLESet (K : Type u) [Field K] {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) (a : ℕ) :
    Set X :=
  {x | letI : Algebra K (X.residueField x) :=
        ((Scheme.ΓSpecIso (.of K)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
      Algebra.trdeg K (X.residueField x) ≤ a}

/-- For a scheme locally of finite type over a field, the set `E_a` is stable under
specialization: the transcendence degree of the residue field drops strictly along a nontrivial
specialization (Stacks 0A21). -/
theorem Scheme.stableUnderSpecialization_trdegLESet (K : Type u) [Field K] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of K)) [LocallyOfFiniteType f] (a : ℕ) :
    StableUnderSpecialization (Scheme.trdegLESet K f a) := by
  intro x x' hxx' hx
  by_cases hne : x = x'
  · exact hne ▸ hx
  · exact (trdeg_residueField_lt_of_specialization K X f hxx' hne).le.trans hx

/-- A subsheaf of a torsion abelian sheaf is torsion. -/
private theorem torsionSheafProperty_of_mono {C : Type*} [Category* C]
    {J : GrothendieckTopology C} {F G : Sheaf J AddCommGrpCat.{u + 1}} (ι : F ⟶ G) [Mono ι]
    (hG : Stacks.Torsion.torsionSheafProperty J G) : Stacks.Torsion.torsionSheafProperty J F := by
  have : Mono ((sheafToPresheaf J AddCommGrpCat.{u + 1}).map ι) := inferInstance
  have hinj : ∀ U : Cᵒᵖ, Function.Injective (ι.hom.app U) := fun U =>
    (AddCommGrpCat.mono_iff_injective _).1
      (inferInstanceAs (Mono (((sheafToPresheaf J _).map ι).app U)))
  intro U x
  obtain ⟨R, hR, hx⟩ := hG U (ι.hom.app _ x)
  refine ⟨R, hR, fun V f hf => ?_⟩
  obtain ⟨n, hn, hnx⟩ := hx V f hf
  refine ⟨n, hn, hinj _ ?_⟩
  rw [map_nsmul, map_zero]
  rw [← hnx]
  exact congrArg (n • ·) (NatTrans.naturality_apply ι.hom f.op x)

/-- **Stacks 0F0W, given Stacks 0F0V in dimensions at most `a`** (Interlude II of the proof of
Stacks 0F0V). Let `K` be a field, `X` an affine scheme of finite type over `K`, and `a` a natural
number such that every affine scheme `Z` of finite type over `K` with `dim Z ≤ a` has
`cd(Z) ≤ a + cd(K)` (`hV`). Let `𝓕` be a torsion abelian sheaf on `X_ét` whose support is
contained in the set `E_a` of points `x` with `trdeg_K κ(x) ≤ a`. Then `H^b(X, 𝓕) = 0` for
`b > a + cd(K)`. -/
theorem subsingleton_H_of_smallEtaleSupport_subset_of_cdBound (K : Type u) [Field K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of K)) [IsAffine X] [LocallyOfFiniteType f] (a : ℕ)
    (hV : ∀ (Z : Scheme.{u}) (g : Z ⟶ Spec (.of K)) [IsAffine Z] [LocallyOfFiniteType g],
      topologicalKrullDim Z ≤ a →
        Scheme.etaleCohomologicalDimension Z ≤
          a + Scheme.etaleCohomologicalDimension (Spec (.of K)))
    (F : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty X.smallEtaleTopology F)
    (hsupp : Stacks.EtaleCohomology.smallEtaleSupport F ⊆ Scheme.trdegLESet K f a)
    (b : ℕ) (hb : (a : ℕ∞) + Scheme.etaleCohomologicalDimension (Spec (.of K)) < b) :
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
      torsionSheafProperty_of_mono (ι.app i) hF
    have hH : Stacks.Torsion.torsionSheafProperty J.subscheme.smallEtaleTopology H :=
      Stacks.Torsion.torsionSheafProperty_of_iso _
        ((smallEtalePullbackAbIsoEtaleAbelianInverseImage i₀).app (D.obj i)).symm
        (torsionSheafProperty_etaleAbelianInverseImage.{u, u + 1} i₀ (D.obj i) hDtors)
    have : IsAffine J.subscheme := isAffine_of_isAffineHom i₀
    -- the closed subscheme has dimension at most `a`
    have hdim : topologicalKrullDim J.subscheme ≤ a := by
      rw [topologicalKrullDim_eq_iSup_trdeg_residueField K J.subscheme (i₀ ≫ f)]
      refine iSup_le fun z => ?_
      have htr := trdeg_residueField_of_surjectiveOnStalks K f i₀ z.1
      have hz : i₀ z.1 ∈ E := hWE (hrange ▸ ⟨z.1, rfl⟩)
      simp only [E, Scheme.trdegLESet, Set.mem_ofPred_eq] at hz
      rw [htr] at hz
      exact_mod_cast Cardinal.toENat_le_natCast.2 hz
    have hcd := hV J.subscheme (i₀ ≫ f) hdim
    have h1 : Subsingleton (Sheaf.H.{u + 1, u + 1} H b) :=
      Scheme.isEtaleCohomologyBound_etaleCohomologicalDimension _ _ hH b
        (lt_of_le_of_lt hcd hb)
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
