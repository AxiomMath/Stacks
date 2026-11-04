module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ChowOperationsCompatibility
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.ChernClassesIntertwining
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChern.SplittingTower

/-!
# Segre and Chern operations of projective bundles under flat base change

In Situation 0EDT let `(π : P ⟶ X, 𝒪_P(1))` and `(π' : P' ⟶ Y, 𝒪_{P'}(1))` be projective bundle
data of the same fibre dimension `d` over good algebraic spaces, `f : Y ⟶ X` flat of relative
dimension `r`, and suppose that `P' = Y ×_X P` by a morphism `f' : P' ⟶ P` with
`f'^*𝒪_P(1) ≅ 𝒪_{P'}(1)`. Then flat pullback intertwines the Segre operations,
`t_i(P') ∘ f^* = f^* ∘ t_i(P)`, hence the Chern operations. The three compatibilities which enter
are Stacks 0EPD (flat pullback commutes with proper pushforward), Stacks 0EQR (flat pullback
commutes with the cap product with `c₁`) and Stacks 0EPA (flat pullbacks compose), on Chow
homology; this is the part of the bivariance of Chern classes (Stacks 0ERY) concerning flat
pullback.

For `f` the identity, the flat pullback is the identity, so projective bundle data identified by
an isomorphism over `X` respecting the twists have the same Segre and Chern operations.

## Main results

* `AlgebraicGeometry.Space.PrivateChern.flatPullbackChow_id`: flat pullback along the identity.
* `AlgebraicGeometry.Space.PrivateChern.ProjectiveBundleDatum.segreCap_flatPullbackChow`: flat
  base change of the Segre operations.
* `AlgebraicGeometry.Space.PrivateChern.ProjectiveBundleDatum.chernCap_flatPullbackChow`: flat
  base change of the Chern operations.
* `AlgebraicGeometry.Space.PrivateChern.ProjectiveBundleDatum.chernCap_eq_of_isPullback_id`:
  projective bundle data identified over `X` compatibly with the twists have the same Chern
  operations.

## References

* [Stacks Project, Tag 0ERY](https://stacks.math.columbia.edu/tag/0ERY)
* [Stacks Project, Tag 0EPD](https://stacks.math.columbia.edu/tag/0EPD)
* [Stacks Project, Tag 0EQR](https://stacks.math.columbia.edu/tag/0EQR)
* [Stacks Project, Tag 0EPA](https://stacks.math.columbia.edu/tag/0EPA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.PrivateChern

variable {D : BaseSpaceDimensionSituation.{u}}

/-- **Flat pullback along the identity is the identity** on Chow homology. -/
theorem flatPullbackChow_id {X : D.Ambient} (sX : X ⟶ D.space) (hX : D.IsGood sX)
    (hflat : IsFlat D.site D.base D.base_mem (𝟙 X))
    (hr : HasRelativeDimension 0 D.site D.base D.base_mem (𝟙 X))
    (α : chowHomology.{u, u + 1} D sX hX) :
    flatPullbackChow.{u, u + 1} D sX hX sX hX (𝟙 X) (Category.id_comp sX) 0 hflat hr α = α := by
  refine DFunLike.congr_fun (chowHomology_hom_ext (φ :=
    flatPullbackChow.{u, u + 1} D sX hX sX hX (𝟙 X) (Category.id_comp sX) 0 hflat hr)
    (ψ := AddMonoidHom.id _) D sX hX fun k b => ?_) α
  rw [flatPullbackChow_of_chowClass_eq D sX hX sX hX (𝟙 X) (Category.id_comp sX) 0 hflat hr k k
    (by simp)]
  exact of_chowClass_congr D sX hX rfl _ _ (flatPullbackMap_id D sX hX hflat hr k k _ b)

namespace ProjectiveBundleDatum

variable {X Y : D.Ambient} {sX : X ⟶ D.space} {hX : D.IsGood sX} {sY : Y ⟶ D.space}
  {hY : D.IsGood sY} {d : ℕ} (P : ProjectiveBundleDatum D sX hX d)
  (P' : ProjectiveBundleDatum D sY hY d) {f : Y ⟶ X} (hf : f ≫ sX = sY) (r : ℕ)
  (hflat : IsFlat D.site D.base D.base_mem f)
  (hr : HasRelativeDimension r D.site D.base D.base_mem f) {f' : P'.space ⟶ P.space}
  (sq : IsPullback f' P'.proj P.proj f)

include hf sq in
/-- The base change `f' : P' ⟶ P` lies over the base. -/
theorem toBase_eq_of_isPullback : f' ≫ P.toBase = P'.toBase := by
  rw [← P.proj_comp, ← Category.assoc, sq.w, Category.assoc, hf, P'.proj_comp]

include hf hflat hr sq in
/-- The base change `f' : P' ⟶ P` of a flat morphism of relative dimension `r` is flat of
relative dimension `r`. -/
theorem isFlat_and_hasRelativeDimension_of_isPullback :
    IsFlat D.site D.base D.base_mem f' ∧ HasRelativeDimension r D.site D.base D.base_mem f' :=
  (AlgebraicGeometry.Space.isFlat_and_hasRelativeDimension_of_isPullback D P'.toBase P'.isGood
    P.toBase P.isGood sY hY sX hX (toBase_eq_of_isPullback P P' hf sq) hf sq r hflat hr).2

include sq in
/-- **Flat base change of the Segre operations**: if `P' = Y ×_X P` by `f'` with
`f'^*𝒪_P(1) ≅ 𝒪_{P'}(1)`, then `t_i(P') ∘ f^* = f^* ∘ t_i(P)` on `CH_*(X)`. -/
theorem segreCap_flatPullbackChow
    (e : pullbackLine D P'.toBase P'.isGood P.toBase P.isGood f' P.twist ≅ P'.twist) (i : ℕ)
    (α : chowHomology.{u, u + 1} D sX hX) :
    P'.segreCap i (flatPullbackChow.{u, u + 1} D sY hY sX hX f hf r hflat hr α) =
      flatPullbackChow.{u, u + 1} D sY hY sX hX f hf r hflat hr (P.segreCap i α) := by
  have hf' := isFlat_and_hasRelativeDimension_of_isPullback P P' hf r hflat hr sq
  have hbase := toBase_eq_of_isPullback P P' hf sq
  refine segreCap_apply_of_compatible P P'
    (flatPullbackChow.{u, u + 1} D sY hY sX hX f hf r hflat hr)
    (flatPullbackChow.{u, u + 1} D P'.toBase P'.isGood P.toBase P.isGood f' hbase r hf'.1 hf'.2)
    (fun β => ?_) (fun β => ?_) (fun α => ?_) i α
  · exact flatPullbackChow_properPushforwardChow D P'.toBase P'.isGood P.toBase P.isGood sY hY sX
      hX hbase P'.proj_comp P.proj_comp hf r hflat hr hf'.1 hf'.2 sq P.isProper P'.isProper β
  · refine (flatPullbackChow_firstChernCapChow D P'.toBase P'.isGood P.toBase P.isGood f' hbase r
      hf'.1 hf'.2 P.twist P.isInvertible_twist β).trans ?_
    exact DFunLike.congr_fun (firstChernCapChow_congr_iso D P'.toBase P'.isGood _ _ _
      P'.isInvertible_twist e) _
  · exact flatPullbackChow_flatPullbackChow_of_comm D P'.toBase P'.isGood P.toBase P.isGood sY hY
      sX hX sq.w hbase P.proj_comp P'.proj_comp hf r d d r (Nat.add_comm r d) hf'.1 hf'.2 P.isFlat
      P.hasRelativeDimension P'.isFlat P'.hasRelativeDimension hflat hr α

include sq in
/-- **Flat base change of the Chern operations** of projective bundle data. -/
theorem chernCap_flatPullbackChow
    (e : pullbackLine D P'.toBase P'.isGood P.toBase P.isGood f' P.twist ≅ P'.twist) (n : ℕ)
    (α : chowHomology.{u, u + 1} D sX hX) :
    P'.chernCap n (flatPullbackChow.{u, u + 1} D sY hY sX hX f hf r hflat hr α) =
      flatPullbackChow.{u, u + 1} D sY hY sX hX f hf r hflat hr (P.chernCap n α) :=
  (map_chernSeq_of_intertwines (flatPullbackChow.{u, u + 1} D sY hY sX hX f hf r hflat hr)
    (fun i α => (segreCap_flatPullbackChow P P' hf r hflat hr sq e i α).symm) n α).symm

end ProjectiveBundleDatum

/-- **Projective bundle data identified over `X` compatibly with the twists have the same Chern
operations**: if `f' : P' ⟶ P` is an isomorphism over `X` (a cartesian square over the identity)
with `f'^*𝒪_P(1) ≅ 𝒪_{P'}(1)`, then `c_n(P') = c_n(P)`. -/
theorem ProjectiveBundleDatum.chernCap_eq_of_isPullback_id {X : D.Ambient} {sX : X ⟶ D.space}
    {hX : D.IsGood sX} {d : ℕ} (P P' : ProjectiveBundleDatum D sX hX d)
    {f' : P'.space ⟶ P.space} (sq : IsPullback f' P'.proj P.proj (𝟙 X))
    (e : pullbackLine D P'.toBase P'.isGood P.toBase P.isGood f' P.twist ≅ P'.twist) (n : ℕ) :
    P'.chernCap.{u, u + 1} n = P.chernCap n := by
  have het : IsEtale D.site D.base D.base_mem (𝟙 X) := isEtale_of_isIso D.site D.base D.base_mem _
  have hflat := isFlat_of_isEtale D.site D.base D.base_mem het
  have hr := hasRelativeDimension_zero_of_isEtale D.site D.base D.base_mem (𝟙 X) hX.1 het
  refine AddMonoidHom.ext fun α => ?_
  have h := P.chernCap_flatPullbackChow P' (Category.id_comp sX) 0 hflat hr sq e n α
  rwa [flatPullbackChow_id, flatPullbackChow_id] at h

end AlgebraicGeometry.Space.PrivateChern

end
