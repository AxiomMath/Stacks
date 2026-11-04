module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ProperFlatBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ModificationDomination.LocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.PrincipalizationAtClosedPointsUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeNormalization
public import StacksFrontier.AlgebraicGeometry.Spaces.SurfaceTransfer.DominationFromNeighborhoods

/-!
# Dominating a modification at regular closed points by blowing up closed points

Let `S` be a scheme, let `X` be a Noetherian algebraic space over `S` and let `T ⊆ |X|` be a
finite set of closed points at each of which `X` is regular with local ring of dimension two. Let
`f : Y ⟶ X` be a proper morphism of algebraic spaces which is an isomorphism over
`U = X ∖ T`. **Stacks 0BHH** asserts that there is a sequence

`X_n ⟶ X_{n-1} ⟶ … ⟶ X_1 ⟶ X_0 = X`

in which each `X_{i+1} ⟶ X_i` is the blowing up of `X_i` at a closed point lying above a point
of `T`, and a factorization `X_n ⟶ Y ⟶ X` of the composite.

## Main results

* `AlgebraicGeometry.Space.exists_blowupFactorization_factors_of_isProper`: such a sequence and
  factorization exist (Stacks 0BHH).

## The proof

The source dominates `Y` by a `U`-admissible blowup of `X` (Stacks 087G), makes its centre
invertible by Stacks 0BHG and concludes by the universal property of blowing up (Stacks 085U).
Stacks 087G is available in the library over an affine Noetherian scheme
(`AlgebraicGeometry.Space.exists_isAdmissibleBlowup_dominating_of_isAffine`), so the argument is
run on the elementary étale neighbourhoods `(Uᵢ, uᵢ) ⟶ (X, xᵢ)` of Section 0BH9 and transported
back to `X` exactly as in the source's proof of Stacks 0BHG, of which it is the same argument
with one more step:

* over the affine Noetherian scheme `Uᵢ` the base change `Y ×_X Uᵢ ⟶ Uᵢ` is proper and an
  isomorphism over `Uᵢ ∖ {uᵢ}`, so it is dominated by the blowup `S'ᵢ ⟶ Uᵢ` in a closed
  subspace `Zᵢ` supported at `uᵢ` (Stacks 087G);
* the scheme case of Stacks 0BHG, Stacks 0AHH, gives a sequence of blowups of `Uᵢ` at closed
  points over `uᵢ` on whose top the ideal of `Zᵢ` is invertible, so that the top maps to `S'ᵢ`,
  hence to `Y ×_X Uᵢ`, over `Uᵢ` (Stacks 085U);
* these sequences lift to one sequence `X_n ⟶ … ⟶ X` of blowings up at closed points over `T`
  (Stacks 0BHF,
  `AlgebraicGeometry.Space.ClosedPointNeighborhoods.exists_blowupFactorization_stageRep`);
* `X_n` and `Y` are both isomorphisms over `X ∖ T`, and the maps over the `Uᵢ` glue to a map
  `X_n ⟶ Y` over `X` by the fullness of the functor of Stacks 0BHA (Stacks 0BHB,
  `AlgebraicGeometry.Space.ClosedPointNeighborhoods.exists_hom_of_forall_pullback_hom`).

## Implementation notes

The open subspace `U = X ∖ T` is `AlgebraicGeometry.Space.openSubspaceOfPoints` of the
complement of `T`, "`f` is an isomorphism over `U`" is invertibility of the base change
`f⁻¹(U) ⟶ U`, and the sequence is `AlgebraicGeometry.Space.BlowupFactorization` with centres
over `T`, as in Stacks 0BHG.

## References

* [Stacks Project, Tag 0BHH](https://stacks.math.columbia.edu/tag/0BHH)
* [Stacks Project, Tag 0BHG](https://stacks.math.columbia.edu/tag/0BHG)
* [Stacks Project, Tag 087G](https://stacks.math.columbia.edu/tag/087G)
* [Stacks Project, Tag 085U](https://stacks.math.columbia.edu/tag/085U)
* [Stacks Project, Tag 0BHB](https://stacks.math.columbia.edu/tag/0BHB)
* [Stacks Project, Tag 0AHH](https://stacks.math.columbia.edu/tag/0AHH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Dominating a modification by blowing up closed points.** Let `S` be a scheme, let `X` be a
Noetherian algebraic space over `S` and let `T ⊆ |X|` be a finite set of closed points `x` such
that `X` is regular at `x` and the local ring of `X` at `x` has dimension `2`. Let `f : Y ⟶ X` be
a proper morphism of algebraic spaces which is an isomorphism over `U = X ∖ T`. **Then there
exist a sequence**

`X_n ⟶ X_{n-1} ⟶ … ⟶ X_1 ⟶ X_0 = X`

**where `X_{i+1} ⟶ X_i` is the blowing up of `X_i` at a closed point `x_i` lying above a point
of `T`, and a factorization `X_n ⟶ Y ⟶ X` of the composition.** -/
@[stacks 0BHH]
theorem exists_blowupFactorization_factors_of_isProper
    (hterm : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hX : IsNoetherian B S hS hterm X.1)
    (T : Set (points B S hS X.1)) (hTfinite : T.Finite)
    (hTclosed : ∀ x ∈ T, IsClosed ({x} : Set (points B S hS X.1)))
    (hTregular : ∀ x ∈ T, IsRegularAt B S hS X.1 x)
    (hTdim : ∀ x ∈ T, localRingDimension B S hS x = 2)
    (Y : AlgebraicSpaces B S hS) (f : Y ⟶ X) (hf : IsProper B S hS f.hom)
    (hfU : IsIso (pullback.snd f.hom (openSubspaceOfPoints B S hS X.1 Tᶜ).ι)) :
    ∃ (X' : AlgebraicSpaces B S hS) (b : X' ⟶ X),
      Nonempty (BlowupFactorization B S hS T b) ∧ ∃ h : X' ⟶ Y, h ≫ f = b := by
  classical
  let : HasSheafify (BigFppfOver.topology B S hS) (Type u) :=
    AlgebraicGeometry.hasSheafify_bigFppfOver B S hS
  have hdec : IsDecentSpace B S hS X.obj := isDecentSpace_of_isNoetherian B S hS hterm X.property hX
  obtain ⟨n, pt, hrange⟩ := hTfinite.fin_embedding
  have hptT (i : Fin n) : pt i ∈ T := hrange.subset (Set.mem_range_self i)
  let D := ClosedPointNeighborhoods.ofPoints X hdec pt pt.injective fun i => hTclosed _ (hptT i)
  let l : Y ⟶ D.space := f
  have hl : IsIso (pullback.snd l.hom D.openAwayFromPoints.ι) := by
    change IsIso (pullback.snd f.hom (openSubspaceOfPoints B S hS X.obj (Set.range pt)ᶜ).ι)
    rwa [hrange]
  have hloc : ∀ i : Fin n, ∃ (Y' : Scheme.{u}) (f' : Y' ⟶ D.neighborhoodScheme i)
      (Zc : ClosedSubspaces B S hS (yoneda.obj (D.neighborhood i).scheme))
      (S' : AlgebraicSpaces B S hS) (b : S' ⟶ schemeSpace (D.neighborhood i).scheme)
      (g' : S'.obj ⟶ pullback l.hom (D.toSpaceHom i).hom),
      Stacks.ResolutionOfSurfaces.PointBlowupChain (D.neighborhoodScheme i)
        {(D.neighborhood i).point} Y' f' ∧
        Stacks.Divisors.IsEffectiveCartierDivisor
          (((BigFppfOver.toScheme B S hS).map (Zc.2.2.rep.snd (𝟙 _))).ker.comap f') ∧
        IsBlowupAlong B S hS Zc b ∧ g' ≫ pullback.snd l.hom (D.toSpaceHom i).hom = b.hom := by
    intro i
    have hpcl := D.isClosed_singleton_neighborhood_point i
    let U₀ : (D.neighborhoodScheme i).Opens := ⟨{(D.neighborhood i).point}ᶜ, hpcl.isOpen_compl⟩
    have hEet := (isEtale_iff_presheaf_of_yoneda B S hS (D.neighborhood i).toSpace).mp
      (D.neighborhood i).etale_toSpace
    have : IsAffine (D.neighborhoodScheme i) := D.isAffine_neighborhood i
    have : IsLocallyNoetherian (D.neighborhoodScheme i) :=
      (exists_atlas_iff_forall_etale B S hS X.obj (fun T : Scheme.{u} => IsLocallyNoetherian T)
        X.property).mp hX.2.2 _ _ hEet
    have : AlgebraicGeometry.IsNoetherian (D.neighborhoodScheme i) := ⟨⟩
    have hset : pointsToScheme B S hS (D.neighborhood i).scheme ⁻¹' (U₀ : Set _) =
        {D.neighborhoodPoint i}ᶜ := by
      ext p
      simp only [Set.mem_preimage, Set.mem_compl_iff]
      change ¬ pointsToScheme B S hS _ p = (D.neighborhood i).point ↔ ¬ p = D.neighborhoodPoint i
      refine not_congr ⟨fun h => injective_pointsToScheme B S hS _ ?_, fun h => ?_⟩
      · rw [h]
        exact (pointsToScheme_presheafPoint B S hS _ _ _).symm
      · rw [h]
        exact pointsToScheme_presheafPoint B S hS _ _ _
    have hiso : IsIso (pullback.snd (pullback.snd l.hom (D.toSpaceHom i).hom)
        (openSubspaceOfPoints B S hS (yoneda.obj (D.neighborhood i).scheme)
          (pointsToScheme B S hS (D.neighborhood i).scheme ⁻¹' (U₀ : Set _))).ι) := by
      rw [hset]
      exact ((D.restrictionComponent i).obj ⟨Over.mk l.hom, Y.property, hl⟩).property.2
    have hYi : IsAlgebraicSpace B S hS (pullback l.hom (D.toSpaceHom i).hom) :=
      isAlgebraicSpace_pullback B S hS _ _ Y.property (D.neighborhoodSpace i).property
        X.property
    have hpr : IsProper B S hS (pullback.snd l.hom (D.toSpaceHom i).hom) :=
      isProper_of_isPullback B S hS hYi Y.property (D.neighborhoodSpace i).property X.property
        (IsPullback.of_hasPullback l.hom (D.toSpaceHom i).hom) hf
    obtain ⟨S', b, ⟨Zc, -, hdisj, hbl⟩, g', hg'⟩ :=
      @exists_isAdmissibleBlowup_dominating_of_isAffine B S hS (D.neighborhood i).scheme _ _ U₀
        (Over.mk (pullback.snd l.hom (D.toSpaceHom i).hom :
          _ ⟶ yoneda.obj (D.neighborhood i).scheme)) hYi hiso hpr
    let Zc' : ClosedSubspaces B S hS (yoneda.obj (D.neighborhood i).scheme) := Zc
    have hdisj' : Disjoint (subspacePointSet B S hS (yoneda.obj (D.neighborhood i).scheme)
        (openSubspaceOfPoints B S hS (yoneda.obj (D.neighborhood i).scheme)
          (pointsToScheme B S hS (D.neighborhood i).scheme ⁻¹' (U₀ : Set _))))
        (subspacePointSet B S hS (yoneda.obj (D.neighborhood i).scheme) Zc'.1) := hdisj
    set s := Zc'.2.2.rep.snd (𝟙 (yoneda.obj (D.neighborhood i).scheme)) with hs
    set J : (D.neighborhoodScheme i).IdealSheafData :=
      ((BigFppfOver.toScheme B S hS).map s).ker with hJ
    have hsupp : (J.support : Set (D.neighborhoodScheme i)) ⊆ {(D.neighborhood i).point} := by
      have : _root_.AlgebraicGeometry.IsClosedImmersion
          ((BigFppfOver.toScheme B S hS).map s) := Zc'.2.2.property_snd _
      rw [hJ, Scheme.Hom.support_ker]
      refine closure_minimal ?_ hpcl
      rintro _ ⟨r, rfl⟩
      have hsq := Zc'.2.2.rep.isPullback (𝟙 (yoneda.obj (D.neighborhood i).scheme))
      have h1 : pointsMap B S hS _ (yoneda.map s) (schemeSpacePoint _ r) =
          schemeSpacePoint (D.neighborhood i).scheme
            ((BigFppfOver.toScheme B S hS).map s r) := by
        simpa using congrFun (pointsMap_yoneda_map_eq B S hS s) (schemeSpacePoint _ r)
      have h2 : schemeSpacePoint (D.neighborhood i).scheme
          ((BigFppfOver.toScheme B S hS).map s r) ∈ subspacePointSet B S hS _ Zc'.1 := by
        rw [← h1, show yoneda.map s = yoneda.map s ≫ 𝟙 (yoneda.obj (D.neighborhood i).scheme)
          from (Category.comp_id _).symm, ← hsq.w, pointsMap_comp_apply]
        exact ⟨_, rfl⟩
      have h4 := Set.disjoint_right.mp hdisj' h2
      rw [subspacePointSet, range_pointsMap_ι_openSubspaceOfPoints, Set.mem_preimage] at h4
      have h5 : pointsToScheme B S hS (D.neighborhood i).scheme (schemeSpacePoint
          (D.neighborhood i).scheme ((BigFppfOver.toScheme B S hS).map s r)) =
          (BigFppfOver.toScheme B S hS).map s r := (pointsEquivScheme B S hS _).apply_symm_apply _
      rw [h5] at h4
      by_contra hne
      exact h4 hne
    obtain ⟨Y', f', hchain, hcart⟩ :=
      Stacks.ResolutionOfSurfaces.exists_pointBlowupChain_principalizing
        ({(D.neighborhood i).point} : Finset (D.neighborhoodScheme i))
        (by simpa using hpcl)
        (by simpa using D.isRegularLocalRing_stalk_neighborhood_point i (hTregular _ (hptT i)))
        (by simpa using D.ringKrullDim_stalk_neighborhood_point i (hTdim _ (hptT i)))
        J (by rwa [Finset.coe_singleton])
    rw [Finset.coe_singleton] at hchain
    exact ⟨Y', f', Zc', S', b, g', hchain, hcart, hbl, hg'⟩
  choose Y' f' Zc S' b g' hchain hcart hbl hg' using hloc
  obtain ⟨A, g, ⟨F⟩, hrep, hiso⟩ := D.exists_blowupFactorization_stageRep hX.2.2 f' hchain
  have hm : ∀ i, ∃ m : pullback g.hom (D.toSpaceHom i).hom ⟶ pullback l.hom (D.toSpaceHom i).hom,
      m ≫ pullback.snd l.hom (D.toSpaceHom i).hom = pullback.snd g.hom (D.toSpaceHom i).hom := by
    intro i
    obtain ⟨W, q, Φ, θ, hΦ, hθ⟩ := hrep i
    have hy : IsPullbackDefined B S hS (schemeSpaceMap q) (Zc i) := by
      refine isEffectiveCartierDivisor_of_hasEffectiveCartierEtaleCover B S hS _ _
        ⟨W, 𝟙 _, isEtale_id B S hS _, isSurjective_id B S hS _, ?_⟩
      refine (isSchemeEffectiveCartierPullback_iff B S hS (schemeSpace W) _ W
        (𝟙 (yoneda.obj W))).2 ?_
      let V : SmallEtale B S hS (schemeSpace W).obj :=
        ⟨CostructuredArrow.mk (𝟙 (yoneda.obj W) : yoneda.obj W ⟶ (schemeSpace W).obj),
          presheaf_etale_of_isEtale B S hS (isEtale_id B S hS _)⟩
      have h1 := schemeKer_snd_preimage B S hS (schemeSpaceMap q) (Zc i) V
      have h2 := schemeKer_snd_comp B S hS (X := schemeSpace (D.neighborhood i).scheme) (Zc i)
        (𝟙 (yoneda.obj (D.neighborhood i).scheme)) q
      have hc : (V.1.hom ≫ (schemeSpaceMap q).hom :
          yoneda.obj W ⟶ (schemeSpace (D.neighborhood i).scheme).obj) =
          yoneda.map q ≫ 𝟙 (yoneda.obj (D.neighborhood i).scheme) :=
        (Category.id_comp _).trans (Category.comp_id _).symm
      have key := h1.trans ((congrArg (fun h : yoneda.obj W ⟶
          (schemeSpace (D.neighborhood i).scheme).obj =>
            ((BigFppfOver.toScheme B S hS).map ((Zc i).2.2.rep.snd h)).ker) hc).trans h2)
      refine (congrArg Stacks.Divisors.IsEffectiveCartierDivisor key).mpr ?_
      rw [← hθ, Scheme.IdealSheafData.comap_comp]
      exact Stacks.Divisors.isPullbackDefined_of_flat θ.hom _ (hcart i)
    obtain ⟨lft, hlft, -⟩ := (hbl i).existsUnique_lift (schemeSpaceMap q) hy
    have hb : lft.hom ≫ (b i).hom = yoneda.map q := congrArg (fun k => k.hom) hlft
    exact ⟨Φ.hom ≫ lft.hom ≫ g' i, (Category.assoc _ _ _).trans ((congrArg (Φ.hom ≫ ·)
      ((Category.assoc _ _ _).trans ((congrArg (lft.hom ≫ ·) (hg' i)).trans hb))).trans hΦ)⟩
  choose m hm using hm
  obtain ⟨h, hh⟩ := D.exists_hom_of_forall_pullback_hom g f hiso hl m hm
  exact ⟨A, g, ⟨F.mono hrange.subset⟩, h, hh⟩

end AlgebraicGeometry.Space

end
