module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.PointBlowupPrincipalization
public import StacksFrontier.AlgebraicGeometry.Spaces.EffectiveCartierEtaleEquiv
public import StacksFrontier.AlgebraicGeometry.Spaces.GenericTrivialization
public import StacksFrontier.AlgebraicGeometry.Spaces.LocalRingDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.PrincipalizationAtClosedPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.SurfaceTransfer.BlowupLocalToGlobal

/-!
# Making an ideal invertible on an algebraic space by blowing up closed points

Let `S` be a scheme, let `X` be a Noetherian algebraic space over `S` and let `T ⊆ |X|` be a
finite set of closed points at each of which `X` is regular with local ring of dimension two.
Let `ℐ ⊆ 𝒪_X` be a quasi-coherent sheaf of ideals with `𝒪_X/ℐ` supported on `T`. **Stacks
0BHG** asserts that there is a sequence

`X_m ⟶ X_{m-1} ⟶ … ⟶ X_1 ⟶ X_0 = X`

in which each `X_{j+1} ⟶ X_j` is the blowing up of `X_j` at a closed point `x_j` lying above a
point of `T`, such that `ℐ𝒪_{X_m}` is an invertible ideal sheaf.

## Main results

* `AlgebraicGeometry.Space.exists_blowupFactorization_isPullbackDefined_of_isNoetherian`:
  **Stacks 0BHG**.

## The proof

Write `T = {x₁, …, xₙ}` and choose elementary étale neighbourhoods `(Uᵢ, uᵢ) ⟶ (X, xᵢ)` as in
Section 0BH9 (`AlgebraicGeometry.Space.ClosedPointNeighborhoods.ofPoints`): `Uᵢ` is an affine
scheme, `uᵢ` is its only point over `xᵢ` and no point of `Uᵢ` lies over `xⱼ` for `j ≠ i`. The
restriction `ℐᵢ = ℐ|_{Uᵢ}` is a quasi-coherent sheaf of ideals of the scheme `Uᵢ` supported at
`uᵢ`, and the local ring of `Uᵢ` at `uᵢ` is regular of dimension two, because these are the
étale-local meanings of the hypotheses at `xᵢ`. The scheme case, Stacks 0AHH
(`Stacks.ResolutionOfSurfaces.exists_pointBlowupChain_principalizing`), gives a sequence of
blowups of `Uᵢ` at closed points over `uᵢ` making `ℐᵢ` invertible. By the direction "from the
`Uᵢ` to `X`" of Stacks 0BHF
(`AlgebraicGeometry.Space.ClosedPointNeighborhoods.exists_blowupFactorization_stageRep`) these
lift to a single sequence `X_m ⟶ … ⟶ X` of blowings up at closed points over `T` whose base
change to each `Uᵢ` is the `i`th sequence. Invertibility of `ℐ𝒪_{X_m}` is then checked étale
locally by Stacks 083C
(`AlgebraicGeometry.Space.hasEffectiveCartierEtalePullbacks_of_pointwise_charts`): at a point of
`X_m` over some `xᵢ` the chart `X_m ×_X Uᵢ`, which is the top of the `i`th sequence, carries the
invertible ideal `ℐᵢ𝒪`; at a point off the inverse image of `ℐ`'s support the ideal is the unit
ideal.

## How the statement is said

As for `AlgebraicGeometry.Space.exists_blowupFactorization_isPullbackDefined`: the
quasi-coherent sheaf of ideals `ℐ` is named by the closed subspace `Z` it cuts out (Stacks 03MB),
"`𝒪_X/ℐ` supported on `T`" is `|Z| ⊆ T`, "`ℐ𝒪_{X_m}` is invertible" is
`AlgebraicGeometry.Space.IsPullbackDefined` of Stacks 083Y for the composite `X_m ⟶ X`, and the
sequence is `AlgebraicGeometry.Space.BlowupFactorization` with centres over `T`.

## Relation to `exists_blowupFactorization_isPullbackDefined`

The induction `AlgebraicGeometry.Space.exists_blowupFactorization_isPullbackDefined` takes three
hypotheses which are not the source's: `blowupExists` (existence of the blowing up
of *every* algebraic space at a closed point), `pullbackOfEffectiveCartier` (an algebraic-space
form of Stacks 0809) and `splitting` (a local form of Stacks 0AGT, for every algebraic space,
against a free colength function). The theorem here discharges all of them by a different route,
the source's: the blowing up exists on a locally Noetherian space
(`AlgebraicGeometry.Space.exists_isBlowupAlong_of_isLocallyNoetherian`), and the local input is
the scheme case Stacks 0AHH, transported along the neighbourhoods of Section 0BH9.

## References

* [Stacks Project, Tag 0BHG](https://stacks.math.columbia.edu/tag/0BHG)
* [Stacks Project, Tag 0BHF](https://stacks.math.columbia.edu/tag/0BHF)
* [Stacks Project, Tag 0BH9](https://stacks.math.columbia.edu/tag/0BH9)
* [Stacks Project, Tag 0AHH](https://stacks.math.columbia.edu/tag/0AHH)
* [Stacks Project, Tag 083C](https://stacks.math.columbia.edu/tag/083C)
* [Stacks Project, Tag 083Y](https://stacks.math.columbia.edu/tag/083Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace ClosedPointNeighborhoods

variable {n : ℕ} (D : ClosedPointNeighborhoods B S hS n)

/-- The distinguished point `uᵢ` is a closed point of the scheme of the `i`th neighbourhood. -/
theorem isClosed_singleton_neighborhood_point (i : Fin n) :
    IsClosed ({(D.neighborhood i).point} : Set (D.neighborhoodScheme i)) := by
  have h := D.isClosed_neighborhoodPoint i
  rw [D.neighborhoodPoint_eq_schemeSpacePoint] at h
  exact isClosed_singleton_of_isClosed_schemeSpacePoint _ h

/-- The local ring of the scheme of the `i`th neighbourhood at `uᵢ` is regular when `X` is
regular at `xᵢ`. -/
theorem isRegularLocalRing_stalk_neighborhood_point (i : Fin n)
    (h : IsRegularAt B S hS D.space.obj (D.point i)) :
    IsRegularLocalRing ((D.neighborhoodScheme i).presheaf.stalk (D.neighborhood i).point) := by
  have hEet := (isEtale_iff_presheaf_of_yoneda B S hS (D.neighborhood i).toSpace).mp
    (D.neighborhood i).etale_toSpace
  have := (isRegularLocalRing_stalk_iff_isRegularAt B S hS D.space.property
    (D.neighborhood i).scheme (D.neighborhood i).toSpace hEet
    (presheafPoint B S hS (D.neighborhood i).scheme (D.neighborhood i).point
      (D.neighborhood i).residueField_contained)).mpr (by rwa [(D.neighborhood i).map_point])
  rwa [pointsToScheme_presheafPoint] at this

/-- The local ring of the scheme of the `i`th neighbourhood at `uᵢ` has the dimension of the local
ring of `X` at `xᵢ` (Stacks 04NA). -/
theorem ringKrullDim_stalk_neighborhood_point (i : Fin n) {d : ℕ∞}
    (h : localRingDimension B S hS (D.point i) = d) :
    ringKrullDim ((D.neighborhoodScheme i).presheaf.stalk (D.neighborhood i).point) =
      (d : WithBot ℕ∞) := by
  have hEet := (isEtale_iff_presheaf_of_yoneda B S hS (D.neighborhood i).toSpace).mp
    (D.neighborhood i).etale_toSpace
  have hall := (hasChartLocalRingDimension_iff_allChartsLocalRingDimension B S hS
    D.space.property (D.point i) d).mp
    ((localRingDimension_eq_iff_hasChartLocalRingDimension B S hS D.space.property _ d).mp h)
  set y := presheafPoint B S hS (D.neighborhood i).scheme (D.neighborhood i).point
    (D.neighborhood i).residueField_contained
  have hc := chartPoint_pointsToScheme B S hS (D.neighborhood i).scheme
    (D.neighborhood i).toSpace y
  rw [pointsToScheme_presheafPoint, (D.neighborhood i).map_point] at hc
  exact hall _ _ _ hEet hc

/-- **The restriction of a closed subspace supported on the chosen points to the `i`th
neighbourhood is supported at `uᵢ`.** The sheaf of ideals that a closed subspace `Z ⊆ X` with
`|Z| ⊆ {x₁, …, xₙ}` induces on the scheme `Uᵢ` has support contained in `{uᵢ}`, because `uᵢ` is
the only point of `Uᵢ` over any of the `xⱼ`. -/
theorem support_ker_rep_snd_toSpace_subset (Z : ClosedSubspaces B S hS D.space.obj)
    (hZ : subspacePointSet B S hS D.space.obj Z.1 ⊆ Set.range D.point) (i : Fin n) :
    ((((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd (D.neighborhood i).toSpace)).ker.support :
      Set (D.neighborhoodScheme i))) ⊆ {(D.neighborhood i).point} := by
  have : _root_.AlgebraicGeometry.IsClosedImmersion
      ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd (D.neighborhood i).toSpace)) :=
    Z.2.2.property_snd _
  rw [Scheme.Hom.support_ker]
  refine closure_minimal ?_ (D.isClosed_singleton_neighborhood_point i)
  rintro _ ⟨r, rfl⟩
  have hsq := Z.2.2.rep.isPullback (D.neighborhood i).toSpace
  have h1 : pointsMap B S hS _ (yoneda.map (Z.2.2.rep.snd (D.neighborhood i).toSpace))
      (schemeSpacePoint _ r) =
      schemeSpacePoint (D.neighborhood i).scheme
        ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd (D.neighborhood i).toSpace) r) := by
    simpa using congrFun (pointsMap_yoneda_map_eq B S hS
      (Z.2.2.rep.snd (D.neighborhood i).toSpace)) (schemeSpacePoint _ r)
  have h2 : pointsMap B S hS _ (D.neighborhood i).toSpace
      (schemeSpacePoint (D.neighborhood i).scheme
        ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd (D.neighborhood i).toSpace) r)) ∈
        Set.range D.point := by
    rw [← h1, ← pointsMap_comp_apply, ← hsq.w, pointsMap_comp_apply]
    exact hZ ⟨_, rfl⟩
  obtain ⟨k, hk⟩ := h2
  have hki : k = i :=
    Classical.byContradiction fun hne => D.map_ne_point i k (Ne.symm hne) _ hk.symm
  subst hki
  have h3 := D.eq_of_map_eq_point k _ hk.symm
  change _ = D.neighborhoodPoint k at h3
  rw [D.neighborhoodPoint_eq_schemeSpacePoint] at h3
  exact (pointsEquivScheme B S hS _).symm.injective h3

/-- **The scheme case on a neighbourhood (Stacks 0AHH).** If `X` is regular at `xᵢ` with local
ring of dimension two, a sequence of blowups of `Uᵢ` at closed points over `uᵢ` makes the ideal
of the restriction of `Z` to `Uᵢ` invertible. -/
private theorem exists_pointBlowupChain_isEffectiveCartierDivisor_ker
    (Z : ClosedSubspaces B S hS D.space.obj)
    (hZ : subspacePointSet B S hS D.space.obj Z.1 ⊆ Set.range D.point) (i : Fin n)
    (hreg : IsRegularAt B S hS D.space.obj (D.point i))
    (hdim : localRingDimension B S hS (D.point i) = 2) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ D.neighborhoodScheme i),
      Stacks.ResolutionOfSurfaces.PointBlowupChain (D.neighborhoodScheme i)
        {(D.neighborhood i).point} Y f ∧
      Stacks.Divisors.IsEffectiveCartierDivisor
        (((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd (D.neighborhood i).toSpace)).ker.comap
          f) := by
  have h := Stacks.ResolutionOfSurfaces.exists_pointBlowupChain_principalizing
    ({(D.neighborhood i).point} : Finset (D.neighborhoodScheme i))
    (by simpa using D.isClosed_singleton_neighborhood_point i)
    (by simpa using D.isRegularLocalRing_stalk_neighborhood_point i hreg)
    (by simpa using D.ringKrullDim_stalk_neighborhood_point i hdim)
    _ (by rw [Finset.coe_singleton]; exact D.support_ker_rep_snd_toSpace_subset Z hZ i)
  simpa only [Finset.coe_singleton] using h

/-- **The chart over a point of the inverse image of `Z`.** Given a space `A ⟶ X` whose base
change to each `Uᵢ` is `fᵢ : Yᵢ ⟶ Uᵢ`, and along which the ideal of `Z|_{Uᵢ}` becomes invertible,
every point of `A` over `Z` has an étale chart `X_m ×_X Uₖ` on which the inverse image of `Z` is
an effective Cartier divisor. -/
private theorem exists_chart_isSchemeEffectiveCartierPullback_preimage
    (Z : ClosedSubspaces B S hS D.space.obj)
    (hZ : subspacePointSet B S hS D.space.obj Z.1 ⊆ Set.range D.point)
    {Y : Fin n → Scheme.{u}} (f : ∀ i, Y i ⟶ D.neighborhoodScheme i)
    (hcart : ∀ i, Stacks.Divisors.IsEffectiveCartierDivisor
      (((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd (D.neighborhood i).toSpace)).ker.comap
        (f i)))
    {A : AlgebraicSpaces B S hS} (g : A ⟶ D.space) (hrep : ∀ i, D.StageRep i g (Over.mk (f i)))
    (a : points B S hS A.1) (ha : a ∈ subspacePointSet B S hS A.obj (Z.1.preimage g.hom)) :
    ∃ (V : BigFppfOver B S hS) (gV : yoneda.obj V ⟶ A.1) (v : points B S hS (yoneda.obj V)),
      IsEtale B S hS gV ∧ pointsMap B S hS (yoneda.obj V) gV v = a ∧
        IsSchemeEffectiveCartierPullback B S hS A
          ⟨Z.1.preimage g.hom, isClosedSubspace_preimage B S hS g.hom Z.1 D.space.2 A.2 Z.2⟩
          V gV := by
  set Z' : ClosedSubspaces B S hS A.1 :=
    ⟨Z.1.preimage g.hom, isClosedSubspace_preimage B S hS g.hom Z.1 D.space.2 A.2 Z.2⟩
  obtain ⟨k, hk⟩ := hZ (Eq.mp (congrArg (a ∈ ·) (subspacePointSet_preimage B S hS g.hom Z.1)) ha)
  obtain ⟨W, q, Φ, θ, hΦ, hθ⟩ := hrep k
  obtain ⟨t, ht, -⟩ := exists_points_of_isPullback B S hS
    (IsPullback.of_hasPullback g.hom (D.toSpaceHom k).hom) a (D.neighborhoodPoint k)
    (by rw [← hk, D.pointsMap_toSpaceHom_neighborhoodPoint])
  let gV : yoneda.obj W ⟶ A.obj := Φ.inv ≫ pullback.fst g.hom (D.toSpaceHom k).hom
  have hgV : IsEtale B S hS gV :=
    isEtale_comp B S hS (isEtale_of_iso B S hS Φ.symm)
      (isEtale_pullback_fst B S hS A.property D.space.property (D.neighborhoodSpace k).property
        _ _ (D.neighborhood k).etale_toSpace)
  refine ⟨W, gV, pointsMap B S hS _ Φ.hom t, hgV, ?_, ?_⟩
  · change pointsMap B S hS _ (Φ.inv ≫ pullback.fst g.hom (D.toSpaceHom k).hom)
      (pointsMap B S hS _ Φ.hom t) = a
    rwa [← pointsMap_comp_apply, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]
  rw [isSchemeEffectiveCartierPullback_iff]
  have h1 : ((BigFppfOver.toScheme B S hS).map (Z'.2.2.rep.snd gV)).ker =
      ((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd (gV ≫ g.hom))).ker :=
    schemeKer_snd_preimage B S hS g Z
      ⟨CostructuredArrow.mk gV, presheaf_etale_of_isEtale B S hS hgV⟩
  have h' : Φ.inv ≫ pullback.snd g.hom (D.toSpaceHom k).hom = yoneda.map q :=
    (congrArg (Φ.inv ≫ ·) hΦ).symm.trans (Iso.inv_hom_id_assoc Φ _)
  have hcomp : gV ≫ g.hom = yoneda.map q ≫ (D.neighborhood k).toSpace := by
    calc gV ≫ g.hom = Φ.inv ≫ (pullback.fst g.hom (D.toSpaceHom k).hom ≫ g.hom) :=
          Category.assoc _ _ _
      _ = Φ.inv ≫ (pullback.snd g.hom (D.toSpaceHom k).hom ≫ (D.toSpaceHom k).hom) := by
          rw [pullback.condition]
      _ = (Φ.inv ≫ pullback.snd g.hom (D.toSpaceHom k).hom) ≫ (D.toSpaceHom k).hom :=
          (Category.assoc _ _ _).symm
      _ = yoneda.map q ≫ (D.neighborhood k).toSpace := by rw [h']; rfl
  have hcomp' : (gV ≫ g.hom : yoneda.obj W ⟶ D.space.obj) =
      yoneda.map q ≫ (D.neighborhood k).toSpace := hcomp
  rw [h1, hcomp']
  refine (congrArg Stacks.Divisors.IsEffectiveCartierDivisor
    (schemeKer_snd_comp B S hS Z (D.neighborhood k).toSpace q)).mpr ?_
  show Stacks.Divisors.IsEffectiveCartierDivisor
    ((((BigFppfOver.toScheme B S hS).map (Z.2.2.rep.snd (D.neighborhood k).toSpace)).ker).comap
      ((BigFppfOver.toScheme B S hS).map q))
  rw [← hθ, Scheme.IdealSheafData.comap_comp]
  exact Stacks.Divisors.isPullbackDefined_of_flat θ.hom _ (hcart k)

end ClosedPointNeighborhoods

/-- Let `S` be a scheme, let `X` be a Noetherian algebraic space over `S` and let `T ⊆ |X|` be a
finite set of closed points `x` such that `X` is regular at `x` and the local ring of `X` at `x`
has dimension `2`. Let `ℐ ⊆ 𝒪_X` be a quasi-coherent sheaf of ideals, given by the closed
subspace `Z ⊆ X` it cuts out, such that `𝒪_X/ℐ` is supported on `T`, that is, `|Z| ⊆ T`. **Then
there is a sequence**

`X_m ⟶ X_{m-1} ⟶ … ⟶ X_1 ⟶ X_0 = X`

**where `X_{j+1} ⟶ X_j` is the blowing up of `X_j` at a closed point `x_j` lying above a point
of `T`, such that `ℐ𝒪_{X_m}` is an invertible ideal sheaf** — that is, such that the inverse
image of `Z` along the composite `X_m ⟶ X` is an effective Cartier divisor. -/
@[stacks 0BHG "the lemma in full, with the source's hypotheses and conclusion and nothing
carried"]
theorem exists_blowupFactorization_isPullbackDefined_of_isNoetherian
    (hterm : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hX : IsNoetherian B S hS hterm X.1)
    (T : Set (points B S hS X.1)) (hTfinite : T.Finite)
    (hTclosed : ∀ x ∈ T, IsClosed ({x} : Set (points B S hS X.1)))
    (hTregular : ∀ x ∈ T, IsRegularAt B S hS X.1 x)
    (hTdim : ∀ x ∈ T, localRingDimension B S hS x = 2)
    (Z : ClosedSubspaces B S hS X.1)
    (hZsupport : subspacePointSet B S hS X.1 Z.1 ⊆ T) :
    ∃ (Y : AlgebraicSpaces B S hS) (f : Y ⟶ X),
      Nonempty (BlowupFactorization B S hS T f) ∧ IsPullbackDefined B S hS f Z := by
  classical
  let : HasSheafify (BigFppfOver.topology B S hS) (Type u) :=
    AlgebraicGeometry.hasSheafify_bigFppfOver B S hS
  obtain ⟨n, pt, hrange⟩ := hTfinite.fin_embedding
  have hptT (i : Fin n) : pt i ∈ T := hrange ▸ ⟨i, rfl⟩
  let D := ClosedPointNeighborhoods.ofPoints X
    (isDecentSpace_of_isNoetherian B S hS hterm X.property hX) pt pt.injective
    fun i => hTclosed _ (hptT i)
  have hZD : subspacePointSet B S hS D.space.obj Z.1 ⊆ Set.range D.point := by
    change subspacePointSet B S hS X.obj Z.1 ⊆ Set.range pt
    rwa [hrange]
  choose Y f hf hcart using fun i => D.exists_pointBlowupChain_isEffectiveCartierDivisor_ker Z hZD i
    (hTregular _ (hptT i)) (hTdim _ (hptT i))
  obtain ⟨A, g, ⟨F⟩, hrep, -⟩ := D.exists_blowupFactorization_stageRep hX.2.2 f hf
  refine ⟨A, g, ⟨F.mono (by rintro _ ⟨i, rfl⟩; exact hptT i)⟩, ?_⟩
  set Z' : ClosedSubspaces B S hS A.1 :=
    ⟨Z.1.preimage g.hom, isClosedSubspace_preimage B S hS g.hom Z.1 X.2 A.2 Z.2⟩ with hZ'
  refine isEffectiveCartierDivisor_of_hasEffectiveCartierEtalePullbacks B S hS A Z'
    (hasEffectiveCartierEtalePullbacks_of_pointwise_charts B S hS A Z' fun a => ?_)
  by_cases ha : ∃ d : points B S hS Z'.1.toFunctor, pointsMap B S hS Z'.1.toFunctor Z'.1.ι d = a
  · exact D.exists_chart_isSchemeEffectiveCartierPullback_preimage Z hZD f hcart g hrep a ha
  · obtain ⟨V, v, haff, hv, htop⟩ := exists_affine_chart_definingIdealAt_eq_top B S hS A Z' a ha
    exact ⟨V.1.left, V.1.hom, v, isEtale_of_presheaf_etale B S hS V.2, hv,
      isSchemeEffectiveCartierPullback_of_isRegular_span B S hS A Z' V haff 1 isRegular_one
        (htop.trans Ideal.span_singleton_one.symm)⟩

end AlgebraicGeometry.Space

end
