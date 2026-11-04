module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChow.FieldSpaceDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChow.TwistedEulerMixedDifference
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.StructureSheafCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralClosedSubspaceMaps
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportComponentLength

/-!
# Intersection numbers of integral closed subspaces along closed immersions

Let `X` be proper over a field and `i : Y ⟶ X` a closed immersion. For a coherent `𝒪_Y`-module
`G` the mixed differences of twisted Euler characteristics satisfy
`Δ_X(i_*G; L) = Δ_Y(G; L|_Y)`. For an integral closed subspace `W ⊆ Y` with image `i(W) ⊆ X`
this gives `(L₁ ⋯ L_d · i(W))_X = (L₁|_Y ⋯ L_d|_Y · W)_Y`: by Stacks 0EDE both sides are the
intersection number of the reduced closed subspace on the single irreducible component `|i(W)|`,
weighted by the length of `𝒪` at its generic point, which is one.

The form of Stacks 0EDE used allows a closed set of dimension at most `d`: when the dimension is
smaller both sides vanish.

## Main results

* `AlgebraicGeometry.Space.twistedEulerMixedDifference_modulePushforward_of_isClosedImmersion`.
* `AlgebraicGeometry.Space.twistedEulerMixedDifference_eq_finsum_components_of_le`.
* `AlgebraicGeometry.Space.intersectionNumber_integralClosedSubspacePushforward`.
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe u w

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
    (X : AlgebraicSpaces B (Spec (.of k)) hk) (f : X.1 ⟶ yoneda.obj (baseObject k B hk))
    (hf : IsProper B (Spec (.of k)) hk f)

variable {d : ℕ} (L : Fin d → Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    [∀ j, Stacks.SheafOfModules.IsInvertible (structurePresheaf B (Spec (.of k)) hk X.1)
      (Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B (Spec (.of k)) hk X.1 X.2).O).property (L j)]

/-- **The mixed difference of a direct image along a closed immersion** is the mixed difference
on the closed subspace along the inverse images. -/
theorem twistedEulerMixedDifference_modulePushforward_of_isClosedImmersion
    {Y : AlgebraicSpaces B (Spec (.of k)) hk} (i : Y ⟶ X)
    (hi : IsClosedImmersion B (Spec (.of k)) hk i.hom)
    (G : Modules.{u, u} B (Spec (.of k)) hk Y.1 Y.2)
    (hG : IsCoherent B (Spec (.of k)) hk Y.1 Y.2 G) :
    have hfY : IsProper B (Spec (.of k)) hk (i.hom ≫ f) :=
      isProper_comp B (Spec (.of k)) hk Y.2 X.2
        (isAlgebraicSpace_yoneda B (Spec (.of k)) hk (baseObject k B hk)) i.hom f
        (isProper_of_isClosedImmersion B (Spec (.of k)) hk Y.2 X.2 i.hom hi) hf
    haveI := fun j => stacksIsInvertible_modulePullback_obj B (Spec (.of k)) hk i (L j)
    twistedEulerMixedDifference.{u, w} k B hk X f hf
        ((modulePushforward B (Spec (.of k)) hk i).obj G)
        (isCoherent_modulePushforward_of_isClosedImmersion B (Spec (.of k)) hk
          (hasEtaleLocalProperty_isLocallyNoetherian_of_isProper k B hk X.1 X.2 f hf) i hi G hG) L =
      twistedEulerMixedDifference.{u, w} k B hk Y (i.hom ≫ f) hfY G hG
        (fun j => (modulePullback B (Spec (.of k)) hk i).obj (L j)) := by
  intro hfY
  unfold twistedEulerMixedDifference
  refine Finset.sum_congr rfl fun T _ => ?_
  congr 1
  exact eulerCharacteristic_twistedModuleUlift_modulePushforward_of_isClosedImmersion.{u, w}
    k B hk f hf i hi G hG L _

/-- **Stacks 0EDE read on the mixed difference, for a closed set of dimension at most `d`.**
Let `F` be coherent with support inside a closed set `T ⊆ |X|` of dimension `≤ d`. Then
`Δ(F; L₁, …, L_d) = ∑_C length_{x̄_C}(F) (L₁ ⋯ L_d · Z_C)`, the sum over the components of `T` of
dimension `d`; when `dim T < d` both sides vanish. -/
theorem twistedEulerMixedDifference_eq_finsum_components_of_le
    (F : Modules.{u, u} B (Spec (.of k)) hk X.1 X.2) (hF : IsCoherent B (Spec (.of k)) hk X.1 X.2 F)
    {T : Set (points B (Spec (.of k)) hk X.1)} (hT : IsClosed T) (hTd : topologicalKrullDim T ≤ d)
    (x : irreducibleComponents T → GeometricPoint B (Spec (.of k)) hk X.1)
    (hx : ∀ C, IsGenericPoint (x C).image (Subtype.val '' (C : Set T)))
    (hFT : moduleSupportSet B (Spec (.of k)) hk X F ⊆ T) :
    twistedEulerMixedDifference.{u, w} k B hk X f hf F hF L =
      ∑ᶠ (C : {C : irreducibleComponents T //
          topologicalKrullDim (Subtype.val '' (C : Set T)) = d}),
        ((geometricLength B (Spec (.of k)) hk X (x C.1) F).toNat : ℤ) *
          intersectionNumber.{u, w} k B hk X
            (closedSubfunctorSpace B (Spec (.of k)) hk
              (isClosedSubspace_reducedClosedSubspace B (Spec (.of k)) hk X.1 X.2 _
                (closedSetComponentPoints B (Spec (.of k)) hk T hT C.1).isClosed)) d f hf
            (closedSubfunctorι B (Spec (.of k)) hk
              (isClosedSubspace_reducedClosedSubspace B (Spec (.of k)) hk X.1 X.2 _
                (closedSetComponentPoints B (Spec (.of k)) hk T hT C.1).isClosed))
            (isClosedSubspace_reducedClosedSubspace B (Spec (.of k)) hk X.1 X.2 _
              (closedSetComponentPoints B (Spec (.of k)) hk T hT C.1).isClosed).2
            ((dimension_reducedClosedSubspace B (Spec (.of k)) hk X.1 X.2
              (isDecentSpace_of_isProper_baseObject k B hk X.1 X.2 f hf) _ _).trans C.2) L := by
  rcases hTd.lt_or_eq with hlt | heq
  · have hempty : IsEmpty {C : irreducibleComponents T //
        topologicalKrullDim (Subtype.val '' (C : Set T)) = d} := by
      refine ⟨fun C => ?_⟩
      have hle : topologicalKrullDim (Subtype.val '' (C.1 : Set T)) ≤ topologicalKrullDim T :=
        (Topology.IsEmbedding.inclusion
          (Subtype.coe_image_subset _ _)).isInducing.topologicalKrullDim_le
      rw [C.2] at hle
      exact absurd hlt (not_lt.2 hle)
    rw [finsum_of_isEmpty]
    exact twistedEulerMixedDifference_eq_zero_of_lt.{u, w} k B hk X f hf L F hF
      (((Topology.IsEmbedding.inclusion hFT).isInducing.topologicalKrullDim_le).trans_lt hlt)
  · exact twistedEulerMixedDifference_eq_finsum_components.{u, w} k B hk X f hf L F hF
      hT heq x hx hFT

/-- **Intersection numbers of an integral closed subspace along a closed immersion.** For a closed
immersion `i : Y ⟶ X` and an integral closed subspace `W ⊆ Y` of dimension `d` with image
`i(W) ⊆ X`, `(L₁ ⋯ L_d · i(W))` computed on `X` is `(L₁|_Y ⋯ L_d|_Y · W)` computed on `Y`. -/
theorem intersectionNumber_integralClosedSubspacePushforward
    {Y : AlgebraicSpaces B (Spec (.of k)) hk} (i : Y ⟶ X)
    (hi : IsClosedImmersion B (Spec (.of k)) hk i.hom)
    (W : IntegralClosedSubspace B (Spec (.of k)) hk Y.1)
    (hW : dimension B (Spec (.of k)) hk W.subspace.toFunctor W.isClosedSubspace.1 = d)
    (hP : dimension B (Spec (.of k)) hk
      (IntegralClosedSubspace.pushforward B (Spec (.of k)) hk X.2 Y.2
        (isDecentSpace_of_isProper_baseObject k B hk X.1 X.2 f hf) hi W).subspace.toFunctor
      (IntegralClosedSubspace.pushforward B (Spec (.of k)) hk X.2 Y.2
        (isDecentSpace_of_isProper_baseObject k B hk X.1 X.2 f hf) hi W).isClosedSubspace.1 = d) :
    have hfY : IsProper B (Spec (.of k)) hk (i.hom ≫ f) :=
      isProper_comp B (Spec (.of k)) hk Y.2 X.2
        (isAlgebraicSpace_yoneda B (Spec (.of k)) hk (baseObject k B hk)) i.hom f
        (isProper_of_isClosedImmersion B (Spec (.of k)) hk Y.2 X.2 i.hom hi) hf
    haveI := fun j => stacksIsInvertible_modulePullback_obj B (Spec (.of k)) hk i (L j)
    intersectionNumber.{u, w} k B hk X
        (closedSubspaceToSpace B (Spec (.of k)) hk X
          ⟨(IntegralClosedSubspace.pushforward B (Spec (.of k)) hk X.2 Y.2
            (isDecentSpace_of_isProper_baseObject k B hk X.1 X.2 f hf) hi W).subspace,
          (IntegralClosedSubspace.pushforward B (Spec (.of k)) hk X.2 Y.2
            (isDecentSpace_of_isProper_baseObject k B hk X.1 X.2 f hf) hi W).isClosedSubspace⟩)
        d f hf
        (closedSubspaceInclusion B (Spec (.of k)) hk X
          ⟨(IntegralClosedSubspace.pushforward B (Spec (.of k)) hk X.2 Y.2
            (isDecentSpace_of_isProper_baseObject k B hk X.1 X.2 f hf) hi W).subspace,
          (IntegralClosedSubspace.pushforward B (Spec (.of k)) hk X.2 Y.2
            (isDecentSpace_of_isProper_baseObject k B hk X.1 X.2 f hf) hi W).isClosedSubspace⟩)
        (IntegralClosedSubspace.pushforward B (Spec (.of k)) hk X.2 Y.2
          (isDecentSpace_of_isProper_baseObject k B hk X.1 X.2 f hf) hi W).isClosedSubspace.2 hP L =
      intersectionNumber.{u, w} k B hk Y
        (closedSubspaceToSpace B (Spec (.of k)) hk Y ⟨W.subspace, W.isClosedSubspace⟩) d
        (i.hom ≫ f) hfY
        (closedSubspaceInclusion B (Spec (.of k)) hk Y ⟨W.subspace, W.isClosedSubspace⟩)
        W.isClosedSubspace.2 hW (fun j => (modulePullback B (Spec (.of k)) hk i).obj (L j)) := by
  intro hfY
  have := fun j => stacksIsInvertible_modulePullback_obj B (Spec (.of k)) hk i (L j)
  have hXdec := isDecentSpace_of_isProper_baseObject k B hk X.1 X.2 f hf
  have hLN := hasEtaleLocalProperty_isLocallyNoetherian_of_isProper k B hk X.1 X.2 f hf
  have hLNY := hasEtaleLocalProperty_isLocallyNoetherian_of_isProper k B hk Y.1 Y.2 (i.hom ≫ f)
    hfY
  set P := IntegralClosedSubspace.pushforward B (Spec (.of k)) hk X.2 Y.2 hXdec hi W with hPdef
  have hG := isCoherent_structureSheafPushforward B (Spec (.of k)) hk hLNY
    (closedSubspaceInclusion B (Spec (.of k)) hk Y ⟨W.subspace, W.isClosedSubspace⟩)
    W.isClosedSubspace.2
  rw [intersectionNumber_eq_twistedEulerMixedDifference,
    intersectionNumber_eq_twistedEulerMixedDifference,
    ← twistedEulerMixedDifference_modulePushforward_of_isClosedImmersion.{u, w} k B hk X f hf L i
      hi _ hG]
  set T := subspacePointSet B (Spec (.of k)) hk X.1 P.subspace with hTdef
  have hTcl : IsClosed T :=
    isClosed_range_pointsMap_integralClosedSubspace B (Spec (.of k)) hk X.2 P
  have hTd : topologicalKrullDim T ≤ d := by
    rw [hTdef, subspacePointSet, ← dimension_eq_topologicalKrullDim_range_of_isClosedImmersion B
      (Spec (.of k)) hk X.2 hXdec P.isClosedSubspace.1 P.subspace.ι P.isClosedSubspace.2, hP]
  have : IrreducibleSpace T := Subtype.irreducibleSpace
    (isIrreducible_range_pointsMap_integralClosedSubspace B (Spec (.of k)) hk P)
  let x : irreducibleComponents T → GeometricPoint B (Spec (.of k)) hk X.1 := fun _ =>
    canonicalGeometricPoint B (Spec (.of k)) hk X.1 (P.ambientGenericPoint B (Spec (.of k)) hk)
  have hx : ∀ C, IsGenericPoint (x C).image (Subtype.val '' (C : Set T)) := by
    intro C
    have hC : (C : Set T) = Set.univ :=
      (Set.ext_iff.1 (irreducibleComponents_eq_singleton (X := T)) _).1 C.2
    rw [hC, Set.image_univ, Subtype.range_coe, canonicalGeometricPoint_image]
    exact P.isGenericPoint_ambientGenericPoint B (Spec (.of k)) hk X.2
  have hFT : moduleSupportSet B (Spec (.of k)) hk X (structureSheafPushforward B (Spec (.of k)) hk
      (closedSubspaceInclusion B (Spec (.of k)) hk X ⟨P.subspace, P.isClosedSubspace⟩)) ⊆ T :=
    (moduleSupportSet_structureSheafPushforward_of_isClosedImmersion B (Spec (.of k)) hk _
      P.isClosedSubspace.2).le
  have hGT : moduleSupportSet B (Spec (.of k)) hk X ((modulePushforward B (Spec (.of k)) hk i).obj
      (structureSheafPushforward B (Spec (.of k)) hk
        (closedSubspaceInclusion B (Spec (.of k)) hk Y ⟨W.subspace, W.isClosedSubspace⟩))) ⊆ T := by
    have hsY := moduleSupportSet_structureSheafPushforward_of_isClosedImmersion B (Spec (.of k)) hk
      (closedSubspaceInclusion B (Spec (.of k)) hk Y ⟨W.subspace, W.isClosedSubspace⟩)
      W.isClosedSubspace.2
    have hcl : IsClosed (moduleSupportSet B (Spec (.of k)) hk Y (structureSheafPushforward B
        (Spec (.of k)) hk
        (closedSubspaceInclusion B (Spec (.of k)) hk Y ⟨W.subspace, W.isClosedSubspace⟩))) := by
      rw [hsY]
      exact isClosed_range_pointsMap_integralClosedSubspace B (Spec (.of k)) hk Y.2 W
    have h := supportOfSheaf_modulePushforward_eq_image_of_isClosedImmersion B (Spec (.of k)) hk i
      hi _ hcl
    refine h.le.trans ?_
    show pointsMap B (Spec (.of k)) hk Y.1 i.hom '' moduleSupportSet B (Spec (.of k)) hk Y _ ⊆ T
    rw [hsY, hTdef, hPdef, IntegralClosedSubspace.subspacePointSet_pushforward]
    rfl
  rw [twistedEulerMixedDifference_eq_finsum_components_of_le.{u, w} k B hk X f hf L _ _ hTcl hTd x
      hx hFT,
    twistedEulerMixedDifference_eq_finsum_components_of_le.{u, w} k B hk X f hf L _ _ hTcl hTd x
      hx hGT]
  refine finsum_congr fun C => ?_
  congr 2
  have h₁ : geometricLength B (Spec (.of k)) hk X (x C.1) (structureSheafPushforward B
      (Spec (.of k)) hk (closedSubspaceInclusion B (Spec (.of k)) hk X
        ⟨P.subspace, P.isClosedSubspace⟩)) = 1 :=
    geometricLength_modulePushforward_unit_eq_one B (Spec (.of k)) hk X P (x C.1)
      (canonicalGeometricPoint_image _ _ _ _ _)
  let x' :=
    canonicalGeometricPoint B (Spec (.of k)) hk Y.1 (W.ambientGenericPoint B (Spec (.of k)) hk)
  have himg : (x C.1).image = (geometricPointMap i.hom x').image := by
    rw [geometricPointMap_image, canonicalGeometricPoint_image, canonicalGeometricPoint_image,
      hPdef, IntegralClosedSubspace.ambientGenericPoint_pushforward]
  have : ((modulePushforward B (Spec (.of k)) hk i).obj (structureSheafPushforward B
      (Spec (.of k)) hk (closedSubspaceInclusion B (Spec (.of k)) hk Y
        ⟨W.subspace, W.isClosedSubspace⟩))).IsQuasicoherentOnSite :=
    (isCoherent_modulePushforward_of_isClosedImmersion B (Spec (.of k)) hk hLN i hi _
      hG).toIsQuasicoherentOnSite
  have h₂ : geometricLength B (Spec (.of k)) hk X (x C.1)
      ((modulePushforward B (Spec (.of k)) hk i).obj (structureSheafPushforward B
        (Spec (.of k)) hk (closedSubspaceInclusion B (Spec (.of k)) hk Y
          ⟨W.subspace, W.isClosedSubspace⟩))) = 1 := by
    rw [geometricLength_eq_of_image_eq B (Spec (.of k)) hk X.2 _ _ himg,
      geometricLength_modulePushforward_of_isClosedImmersion B (Spec (.of k)) hk i hi x']
    exact geometricLength_modulePushforward_unit_eq_one B (Spec (.of k)) hk Y W x'
      (canonicalGeometricPoint_image _ _ _ _ _)
  rw [h₁, h₂]

end AlgebraicGeometry.Space

end
