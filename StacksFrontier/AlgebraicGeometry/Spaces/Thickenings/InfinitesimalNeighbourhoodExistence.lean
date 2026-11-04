module

public import Mathlib.RingTheory.Flat.FaithfullyFlat.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.IdealSheafComapMul
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartIdealSheafPreimage
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceFromQuasicoherentIdeal
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.InfinitesimalNeighbourhood
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineFppfFaithfullyFlat

/-!
# Existence of the first order infinitesimal neighbourhood of a closed subspace

Let `Z` be a closed subspace of an algebraic space `X` over a scheme `S`, with ideal sheaf
`𝓘 ⊆ 𝒪_X`.  The first order infinitesimal neighbourhood of [Stacks Project, Tag 05ZV] is the
closed subspace `N ⊆ X` cut out by `𝓘²`.  This file shows that it exists, in the chart-level
form in which this library states the universal property of the neighbourhood: there is a
closed subspace `N` such that on every étale chart `V` of `X` the kernel ideal sheaf of the
closed immersion `N ×_X V ⟶ V` of schemes is the square of that of `Z ×_X V ⟶ V`.

The neighbourhood is the construction of
`AlgebraicGeometry.Space.firstOrderInfinitesimalNeighbourhood`, applied to a surjective étale
chart `U ⟶ X` and to the sheaf of ideals that `𝓘` induces on `U`.  Its defining ideal is
`𝓘(A)²` on every affine chart `A` lying over `U`, by construction.  That this holds on *every*
affine chart is faithfully flat descent: an affine chart `A` is covered by finitely many affine
charts `A_k` lying over `U`, the product of their rings is faithfully flat over the ring of `A`,
and both sheaves of ideals in question are cartesian on affine charts, so the two ideals of
`𝒪(A)` generate the same ideal in each `𝒪(A_k)`.

## Main results

* `Ideal.eq_of_forall_map_eq`: two ideals generating the same ideal in each member of a finite
  family of algebras with faithfully flat product are equal.
* `AlgebraicGeometry.Space.chartIdeal_eq_pow_of_forall_isAffine_hom`: an identity `K(A) = I(A)ⁿ`
  between sheaves of ideals cartesian on affine charts holds on every affine chart once it holds
  on the affine charts lying over a surjective chart.
* `AlgebraicGeometry.Space.ker_eq_ker_sq_of_forall_isAffine`: the chart-level description of the
  neighbourhood follows from its description on affine charts.
* `AlgebraicGeometry.Space.exists_ker_eq_ker_sq`: **the first order infinitesimal
  neighbourhood exists.**

## References

* [Stacks Project, Tag 05ZV](https://stacks.math.columbia.edu/tag/05ZV)
* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

/-- **Faithfully flat descent of an equality of ideals.**  Two ideals of a commutative ring which
generate the same ideal in each member of a finite family of algebras whose product is faithfully
flat are equal. -/
theorem Ideal.eq_of_forall_map_eq {C : Type u} [CommRing C] {ι : Type v} [Finite ι]
    {D : ι → Type u} [∀ i, CommRing (D i)] [∀ i, Algebra C (D i)]
    [Module.FaithfullyFlat C (∀ i, D i)] {N₁ N₂ : Ideal C}
    (h : ∀ i, N₁.map (algebraMap C (D i)) = N₂.map (algebraMap C (D i))) :
    N₁ = N₂ :=
  (Ideal.eq_of_le_of_forall_map_le (D := D) (N₁ := N₁) (N₂ := N₁ ⊔ N₂) le_sup_left
    fun i => by rw [Ideal.map_sup, h i, sup_idem]).trans
  (Ideal.eq_of_le_of_forall_map_le (D := D) (N₁ := N₂) (N₂ := N₁ ⊔ N₂) le_sup_right
    fun i => by rw [Ideal.map_sup, h i, sup_idem]).symm

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS)

/-- **An identity `K(A) = I(A)ⁿ` of sheaves of ideals descends from the affine charts over a
surjective chart.**  Let `K` and `I` be sheaves of ideals of `𝒪_X` which are cartesian on affine
charts, and let `Uc` be an étale chart of `X` surjective on points.  If `K(A) = I(A)ⁿ` on every
affine chart `A` admitting a morphism to `Uc`, then it holds on every affine chart.

An affine chart `A` is covered by finitely many affine charts `A_k` over `Uc`, with faithfully
flat product of rings; `K(A)` and `I(A)ⁿ` generate `K(A_k)` and `I(A_k)ⁿ` in `𝒪(A_k)`, the two
sheaves being cartesian on affine charts, and those agree. -/
theorem chartIdeal_eq_pow_of_forall_isAffine_hom
    (K I : (SheafOfModules.unit (structureRingSheaf B S hS X)).Submodule)
    (hK : IsCartesianOnAffineCharts K.toSheafOfModules)
    (hI : IsCartesianOnAffineCharts I.toSheafOfModules) (n : ℕ)
    (Uc : SmallEtale B S hS X.1) (hsurj : IsSurjective B S hS Uc.1.hom)
    (h : ∀ A : SmallEtale B S hS X.1,
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj A) →
      (A ⟶ Uc) → chartIdeal B S hS X K A = chartIdeal B S hS X I A ^ n)
    (A : SmallEtale B S hS X.1)
    (hA : IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj A)) :
    chartIdeal B S hS X K A = chartIdeal B S hS X I A ^ n := by
  classical
  obtain ⟨m, z, φ, hzaff, hzmem, -, het⟩ := SmallEtale.exists_finite_affine_etale_ofArrows_le
    B S hS X.1 hA (SmallEtale.coversTop_of_isSurjective B S hS X.1 X.2 Uc hsurj A)
  have _ : IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj A)) :=
    hA
  have _ : ∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS X.1).obj (z i))) := hzaff
  let _ : ∀ i, Algebra Γ((BigFppfOver.toScheme B S hS).obj
      ((SmallEtale.toOver B S hS X.1).obj A), ⊤)
      Γ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS X.1).obj (z i)), ⊤) :=
    fun i => ((BigFppfOver.toScheme B S hS).map
      ((SmallEtale.toOver B S hS X.1).map (φ i))).appTop.hom.toAlgebra
  have hffΓ := _root_.AlgebraicGeometry.faithfullyFlat_pi_gamma_of_ofArrows_mem_fppfPrecoverage
    (fun i => (BigFppfOver.toScheme B S hS).map ((SmallEtale.toOver B S hS X.1).map (φ i)))
    (Scheme.etalePrecoverage_le_fppfPrecoverage _ het) fun _ => rfl
  let _ : ∀ i, Algebra (chartRing B S hS X.1 X.2 A) (chartRing B S hS X.1 X.2 (z i)) :=
    fun i => (chartRestrict (hF := X.2) (φ i)).toAlgebra
  have _ : Module.FaithfullyFlat (chartRing B S hS X.1 X.2 A)
      (∀ i, chartRing B S hS X.1 X.2 (z i)) := hffΓ
  refine Ideal.eq_of_forall_map_eq (D := fun i => chartRing B S hS X.1 X.2 (z i)) fun i => ?_
  obtain ⟨_, ⟨e⟩⟩ := hzmem i
  show Ideal.map (chartRestrict (hF := X.2) (φ i)) (chartIdeal B S hS X K A) =
    Ideal.map (chartRestrict (hF := X.2) (φ i)) (chartIdeal B S hS X I A ^ n)
  rw [chartIdeal_map_of_isCartesianOnAffineCharts B S hS X K hK hA (hzaff i) (φ i), Ideal.map_pow,
    chartIdeal_map_of_isCartesianOnAffineCharts B S hS X I hI hA (hzaff i) (φ i)]
  exact h (z i) (hzaff i) e

/-- **The chart-level description of the first order neighbourhood follows from the affine
one.**  If the defining ideal of `N` is the square of that of `Z` on every affine étale chart,
then on every étale chart `V` the kernel ideal sheaf of `N ×_X V ⟶ V` is the square of that of
`Z ×_X V ⟶ V`: both are the sheaves of ideals that the defining ideal sheaves induce on `V`
(`AlgebraicGeometry.Space.ker_rep_snd_eq_idealSheafDataOfChart`), and their ideals over an
affine open of `V` are the defining ideals over the affine chart that open cuts out. -/
theorem ker_eq_ker_sq_of_forall_isAffine (Z N : ClosedSubspaces B S hS X.1)
    (h : ∀ A : SmallEtale B S hS X.1,
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj A) →
      chartIdeal B S hS X (definingIdealSheaf B S hS X N) A =
        chartIdeal B S hS X (definingIdealSheaf B S hS X Z) A ^ 2)
    (V : SmallEtale B S hS X.1) :
    ((BigFppfOver.toScheme B S hS).map (N.2.2.rep.snd V.1.hom)).ker =
      ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd V.1.hom)).ker ^ 2 := by
  rw [ker_rep_snd_eq_idealSheafDataOfChart B S hS X N V,
    ker_rep_snd_eq_idealSheafDataOfChart B S hS X Z V]
  refine Scheme.IdealSheafData.ext (funext fun W => ?_)
  rw [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply, ideal_idealSheafDataOfChart,
    ideal_idealSheafDataOfChart, openChartIdeal, openChartIdeal,
    h (openChart B S hS X.1 V W.1) W.2, Ideal.map_pow]

/-- **The first order infinitesimal neighbourhood of a closed subspace exists**, in the
chart-level description of [Stacks Project, Tag 05ZV]: for every closed subspace `Z` of an
algebraic space `X` there is a closed subspace `N` of `X` whose kernel ideal sheaf on every étale
chart `V` of `X` is the square of that of `Z`.

`N` is `AlgebraicGeometry.Space.firstOrderInfinitesimalNeighbourhood` for a surjective étale chart
`U ⟶ X` and the sheaf of ideals that the ideal sheaf of `Z` induces on `U`, which is invariant
because it is induced from `X`.  Its defining ideal is the square of that of `Z` on the affine
charts over `U` by construction, hence on all affine charts by
`AlgebraicGeometry.Space.chartIdeal_eq_pow_of_forall_isAffine_hom`, hence on all charts by
`AlgebraicGeometry.Space.ker_eq_ker_sq_of_forall_isAffine`. -/
theorem exists_ker_eq_ker_sq (Z : ClosedSubspaces B S hS X.1) :
    ∃ N : ClosedSubspaces B S hS X.1, ∀ V : SmallEtale B S hS X.1,
      ((BigFppfOver.toScheme B S hS).map (N.2.2.rep.snd V.1.hom)).ker =
        ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd V.1.hom)).ker ^ 2 := by
  obtain ⟨U, φ, hs, he⟩ := X.2.exists_atlas
  have hI := definingIdealSheaf_isCartesianOnAffineCharts B S hS X Z
  have hc := comap_idealSheafDataOfChart B S hS X _ hI (A := ⟨CostructuredArrow.mk φ, he⟩)
    (A' := ⟨CostructuredArrow.mk (yoneda.map (atlasRelationSource B S hS hs) ≫ φ),
      presheaf_etale_atlasRelation B S hS X hs he⟩)
  have hJ : IsInvariantIdealSheaf B S hS hs (idealSheafDataOfChart B S hS X
      (definingIdealSheaf B S hS X Z) hI ⟨CostructuredArrow.mk φ, he⟩) :=
    (hc (ObjectProperty.homMk (CostructuredArrow.homMk (atlasRelationTarget B S hS hs)
      (yoneda_map_atlasRelationSource_comp B S hS hs).symm))).trans
    (hc (ObjectProperty.homMk (CostructuredArrow.homMk (atlasRelationSource B S hS hs) rfl))).symm
  have hNc := isClosedSubspace_nthOrderInfinitesimalNeighbourhood B S hS hs he hJ 1
  refine ⟨⟨_, hNc⟩, ker_eq_ker_sq_of_forall_isAffine B S hS X Z _
    (chartIdeal_eq_pow_of_forall_isAffine_hom B S hS X _ _
      (definingIdealSheaf_isCartesianOnAffineCharts B S hS X _) hI 2
      ⟨CostructuredArrow.mk φ, he⟩
      ((presheafSurjective_iff_isSurjective_yoneda B S hS X.1 X.2 U φ).1 hs)
      fun A hA m => ?_)⟩
  have hT : IsAffineOpen (⊤ : (chartScheme A).Opens) := @isAffineOpen_top _ hA
  have hker := (Scheme.IdealSheafData.ker_subschemeι_app (idealSheafDataOfChart B S hS X
    (definingIdealSheaf B S hS X Z) hI A) ⟨⊤, hT⟩).symm.trans
    (ker_appTop_subschemeι_idealSheafDataOfChart B S hS X _ hI A hA)
  show definingIdealAt B S hS X ⟨_, hNc⟩ (op A) = _
  rw [definingIdealAt_nthOrderInfinitesimalNeighbourhood B S hS hs he hJ 1 hNc A m,
    Stacks.IdealSheaf.comap_pow, comap_idealSheafDataOfChart]
  refine (Scheme.IdealSheafData.ker_subschemeι_app _ ⟨⊤, hT⟩).trans ?_
  rw [Scheme.IdealSheafData.ideal_pow, Pi.pow_apply]
  exact congrArg (· ^ (1 + 1)) hker

end AlgebraicGeometry.Space

end
