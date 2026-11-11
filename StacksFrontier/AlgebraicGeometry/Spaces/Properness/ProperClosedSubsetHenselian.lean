module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.SpecializationOverHenselianPair
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedSubspaceCoincidenceLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.ProperClosedSubspaceStage
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.ProperClosedSubset

/-!
# Closed subsets specializing into a proper part of the closed fibre over a henselian pair

Let `W` be an object of the big fppf site of `S` whose scheme is isomorphic to `Spec A`, with
`(A, I)` a henselian pair, and let `g : X ⟶ h_W` be a separated morphism of finite type from an
algebraic space. Write `|X₀| ⊆ |X|` for the points lying over `V(I)`. Let `T ⊆ |X|` be closed such
that `T ∩ |X₀|` is proper over `W` and every point of `T` specializes to a point of `T ∩ |X₀|`.
Then `T` is proper over `W`.

This is the properness step of the per-degree support clause of the derived form of
Grothendieck's existence theorem proposed in Stacks 0DIR (see the entry for 0DIR in
`errata.md`), there applied to `T = ⋃_{j ≥ i} Supp Hʲ(K)`.

The proof goes through Chow's lemma (Stacks 089J) rather than through a compactification. It gives
a proper surjective `p : h_{X'} ⟶ X` from a scheme with a quasi-compact immersion
`j : X' ⟶ ℙⁿ_W`. Let `V = p⁻¹(T)`, the support of the chart ideal of `T` along `p`. Its part
`F = p⁻¹(T ∩ |X₀|)` over the closed fibre is proper over `W`, hence closed in `ℙⁿ_W`. Every point
of `V` specializes into `F`, since `p` is closed on points. The topological lemma
`AlgebraicGeometry.isClosed_range_comp_of_henselianPair` then shows that `j(V)` is closed in
`ℙⁿ_W`. So the closed subscheme of `X'` cut out by the chart ideal of `T` is a closed subscheme of
`ℙⁿ_W`, hence proper over `W`. It is the base change of `p` to the reduced closed subspace on `T`,
which is therefore proper over `W` (Stacks 08AJ).

## Main results

* `AlgebraicGeometry.Space.isClosed_inter_preimage_closedFibre`: `T ∩ |X₀|` is closed.
* `AlgebraicGeometry.Space.isProperOver_of_forall_specializes_closedFibre`: the theorem.

## References

* [Stacks Project, Tag 0CZD](https://stacks.math.columbia.edu/tag/0CZD)
* [Stacks Project, Tag 089J](https://stacks.math.columbia.edu/tag/089J)
* [Stacks Project, Tag 08AJ](https://stacks.math.columbia.edu/tag/08AJ)
* [Stacks Project, Tag 0DIR](https://stacks.math.columbia.edu/tag/0DIR)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The part `T ∩ |X₀|` of a closed set `T ⊆ |X|` over the closed fibre `V(I)` of
`e : W ≅ Spec A` is closed. -/
theorem isClosed_inter_preimage_closedFibre {W : BigFppfOver B S hS} {A : Type u} [CommRing A]
    (e : (BigFppfOver.toScheme B S hS).obj W ⟶ Spec (.of A)) (I : Ideal A)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (g : X ⟶ yoneda.obj W)
    {T : Set (points B S hS X)} (hT : IsClosed T) :
    IsClosed (T ∩ pointsMap B S hS X g ⁻¹'
      (pointsToScheme B S hS W ⁻¹' (e ⁻¹' PrimeSpectrum.zeroLocus (I : Set A)))) :=
  hT.inter (((PrimeSpectrum.isClosed_zeroLocus _).preimage e.continuous).preimage
    ((schemePointsHomeomorph B S hS W).continuous.comp (continuous_pointsMap B S hS g)))

/-- **A closed subset specializing into a proper part of the closed fibre over a henselian pair
is proper.** Let `e : W ≅ Spec A` with `(A, I)` a henselian pair, and let `g : X ⟶ h_W` be
separated and of finite type. Let `T ⊆ |X|` be closed, with `T ∩ |X₀|` proper over `W`, where
`|X₀|` is the set of points of `X` over `V(I)`, and such that every point of `T` specializes to a
point of `T ∩ |X₀|`. Then `T` is proper over `W`. -/
theorem isProperOver_of_forall_specializes_closedFibre {W : BigFppfOver B S hS}
    (A : Type u) [CommRing A] (I : Ideal A) (hI : HenselianPair A I)
    (e : (BigFppfOver.toScheme B S hS).obj W ⟶ Spec (.of A)) [IsIso e]
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (g : X ⟶ yoneda.obj W) (hsep : IsSeparated B S hS g) (hft : IsFiniteType B S hS g)
    (T : Set (points B S hS X)) (hT : IsClosed T)
    (hT₀ : IsProperOver B S hS hX (isAlgebraicSpace_yoneda B S hS W) g hft.1
      (T ∩ pointsMap B S hS X g ⁻¹'
        (pointsToScheme B S hS W ⁻¹' (e ⁻¹' PrimeSpectrum.zeroLocus (I : Set A))))
      (isClosed_inter_preimage_closedFibre B S hS e I g hT))
    (hspec : ∀ x ∈ T, ∃ y ∈ T ∩ pointsMap B S hS X g ⁻¹'
        (pointsToScheme B S hS W ⁻¹' (e ⁻¹' PrimeSpectrum.zeroLocus (I : Set A))), x ⤳ y) :
    IsProperOver B S hS hX (isAlgebraicSpace_yoneda B S hS W) g hft.1 T hT := by
  classical
  let 𝒯 := BigFppfOver.toScheme B S hS
  set fib : Set (points B S hS (yoneda.obj W)) :=
    pointsToScheme B S hS W ⁻¹' (e ⁻¹' PrimeSpectrum.zeroLocus (I : Set A)) with hfib
  set T₀ := T ∩ pointsMap B S hS X g ⁻¹' fib with hT₀def
  have hT₀c : IsClosed T₀ := isClosed_inter_preimage_closedFibre B S hS e I g hT
  have hWa : IsAffine (𝒯.obj W) := .of_isIso e
  -- Chow's lemma over the affine base.
  obtain ⟨Tb, θ, X', ψ, p, -, hp, hps, hpψ, n, j, hj, hjqc, hjψ⟩ :=
    exists_chowSchemeCover_over_isAffine B S hS W hWa hX g hsep hft
  let P := projectiveSpaceOver n (𝒯.obj Tb)
  have hPT : _root_.AlgebraicGeometry.IsProper (P ↘ 𝒯.obj Tb) := isProper_projectiveSpaceOver n _
  let π : P ⟶ Spec (.of A) := (P ↘ 𝒯.obj Tb) ≫ 𝒯.map θ.hom ≫ e
  have : _root_.AlgebraicGeometry.IsProper π := inferInstance
  -- The closed subspaces on `T` and on `T₀`, and their chart ideals along `p`.
  let D : ClosedSubspaces B S hS X :=
    ⟨reducedClosedSubspace B S hS X hX T hT, isClosedSubspace_reducedClosedSubspace' B S hS hX T hT⟩
  let D₀ : ClosedSubspaces B S hS X :=
    ⟨reducedClosedSubspace B S hS X hX T₀ hT₀c,
      isClosedSubspace_reducedClosedSubspace' B S hS hX T₀ hT₀c⟩
  let K := chartKer B S hS ⟨X, hX⟩ D p
  let K₀ := chartKer B S hS ⟨X, hX⟩ D₀ p
  let hpt := schemePointsHomeomorph B S hS X'
  -- Points of the supports.
  have hmemK : ∀ x, x ∈ K.support ↔ pointsMap B S hS _ p (hpt.symm x) ∈ T := by
    intro x
    have h := (mem_subspacePointSet_iff_mem_support_chartKer B S hS ⟨X, hX⟩ D p
      (hpt.symm x)).symm
    rwa [subspacePointSet, range_pointsMap_ι_reducedClosedSubspace,
      ← schemePointsHomeomorph_apply, Homeomorph.apply_symm_apply] at h
  have hmemK₀ : ∀ x, x ∈ K₀.support ↔ pointsMap B S hS _ p (hpt.symm x) ∈ T₀ := by
    intro x
    have h := (mem_subspacePointSet_iff_mem_support_chartKer B S hS ⟨X, hX⟩ D₀ p
      (hpt.symm x)).symm
    rwa [subspacePointSet, range_pointsMap_ι_reducedClosedSubspace,
      ← schemePointsHomeomorph_apply, Homeomorph.apply_symm_apply] at h
  -- The closed fibre of `X'` is the inverse image of `|X₀|`.
  have hpg : p ≫ g = yoneda.map (ψ ≫ θ.hom) := by
    rw [Functor.map_comp, ← hpψ, Category.assoc, Category.assoc, ← Functor.map_comp,
      Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.comp_id]
  have hfibX : ∀ x, x ∈ (j ≫ π) ⁻¹' PrimeSpectrum.zeroLocus (I : Set A) ↔
      pointsMap B S hS X g (pointsMap B S hS _ p (hpt.symm x)) ∈ fib := by
    intro x
    have h1 : pointsMap B S hS X g (pointsMap B S hS _ p (hpt.symm x)) =
        pointsMap B S hS _ (yoneda.map (ψ ≫ θ.hom)) (hpt.symm x) := by
      rw [← hpg, pointsMap_comp]
      rfl
    have h3 : (P ↘ 𝒯.obj Tb) (j x) = 𝒯.map ψ x := by
      rw [← Scheme.Hom.comp_apply, hjψ]
    have h2 : (j ≫ π) x = e (𝒯.map θ.hom (𝒯.map ψ x)) := by
      simp only [π, Scheme.Hom.comp_apply, h3]
    have h4 : pointsToScheme B S hS W (pointsMap B S hS _ (yoneda.map (ψ ≫ θ.hom)) (hpt.symm x)) =
        𝒯.map θ.hom (𝒯.map ψ x) := by
      rw [pointsToScheme_pointsMap_yoneda, ← schemePointsHomeomorph_apply B S hS X',
        Homeomorph.apply_symm_apply, Functor.map_comp, Scheme.Hom.comp_apply]
    have h5 : (j ≫ π) x = e (pointsToScheme B S hS W
        (pointsMap B S hS _ (yoneda.map (ψ ≫ θ.hom)) (hpt.symm x))) := by
      rw [h4, h2]
    rw [h1]
    exact Iff.of_eq (congrArg (· ∈ PrimeSpectrum.zeroLocus (I : Set A)) h5)
  have hF₀ : (K.support : Set _) ∩ (j ≫ π) ⁻¹' PrimeSpectrum.zeroLocus (I : Set A) =
      K₀.support := by
    ext x
    rw [Set.mem_inter_iff, SetLike.mem_coe, SetLike.mem_coe, hmemK, hmemK₀, hfibX]
    rfl
  -- `j(F)` is closed: `F` is proper over the base.
  have hF : IsClosed (j '' (Set.range K.subschemeι ∩
      (j ≫ π) ⁻¹' PrimeSpectrum.zeroLocus (I : Set A))) := by
    rw [K.range_subschemeι, hF₀, ← K₀.range_subschemeι, ← Set.range_comp]
    have h₀ := isProper_chartKer_subschemeι_comp B S hS hX g θ ψ p hp hpψ D₀ hT₀
    rw [← hjψ, ← Category.assoc] at h₀
    have : _root_.AlgebraicGeometry.IsProper (K₀.subschemeι ≫ j) :=
      _root_.AlgebraicGeometry.IsProper.of_comp _ (P ↘ 𝒯.obj Tb)
    exact (K₀.subschemeι ≫ j).isClosedMap.isClosed_range
  -- Every point of `V` specializes into `F`.
  have hspec' : ∀ t ∈ Set.range K.subschemeι, ∃ v ∈ Set.range K.subschemeι ∩
      (j ≫ π) ⁻¹' PrimeSpectrum.zeroLocus (I : Set A), t ⤳ v := by
    intro t ht
    rw [K.range_subschemeι, SetLike.mem_coe, hmemK] at ht
    obtain ⟨y, hy, hxy⟩ := hspec _ ht
    have hcl : IsClosed (pointsMap B S hS _ p '' closure {hpt.symm t}) :=
      isClosed_of_universallyClosed B S hS hX p hp.2.2 _ isClosed_closure
    obtain ⟨w, hw, hwy⟩ : y ∈ pointsMap B S hS _ p '' closure {hpt.symm t} :=
      closure_minimal (Set.singleton_subset_iff.2
        (Set.mem_image_of_mem _ (subset_closure (Set.mem_singleton _)))) hcl
        (specializes_iff_mem_closure.1 hxy)
    refine ⟨hpt w, ?_, ?_⟩
    · rw [K.range_subschemeι, hF₀, SetLike.mem_coe, hmemK₀, Homeomorph.symm_apply_apply, hwy]
      exact hy
    · have h := (specializes_iff_mem_closure.2 hw).map hpt.continuous
      rwa [Homeomorph.apply_symm_apply] at h
  -- Hence `j(V)` is closed, and `V` is proper over the base.
  have hV := isClosed_range_comp_of_henselianPair A I hI π j K.subschemeι hF hspec'
  have : _root_.AlgebraicGeometry.IsClosedImmersion (K.subschemeι ≫ j) :=
    .of_isPreimmersion _ hV
  have hKp : _root_.AlgebraicGeometry.IsProper (K.subschemeι ≫ 𝒯.map ψ) := by
    rw [← hjψ, ← Category.assoc]
    infer_instance
  exact isProper_ι_comp_of_isProper_rep_fst B S hS hX g hsep hft p hps D
    ((isProper_rep_fst_comp_iff B S hS hX g θ ψ p hpψ D).2 hKp)

end AlgebraicGeometry.Space

end
