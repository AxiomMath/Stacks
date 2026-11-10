module

public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.ComplementaryNodal
public import StacksFrontier.AlgebraicGeometry.Curves.PushoutCompletedLocalRing
public import StacksFrontier.AlgebraicGeometry.Pushout.FiniteType
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.Zero
public import StacksCore.Tactic.StacksAttribute

/-!
# The completed local ring of the contraction of a rational bridge

Let `k` be a field, let `X` be a proper scheme over `k` of dimension one with `H⁰(X, 𝒪_X) = k`
and at-worst-nodal singularities, and let `C ⊆ X` be a rational bridge. Write `X'` for the
scheme-theoretic closure of `X \ C`, `k' = Γ(C, 𝒪_C)` and `k'' = Γ(C ∩ X', 𝒪)`, and let `Y` be
the pushout of `C ∩ X' ⟶ X'` along the collapse `C ∩ X' ⟶ Spec k'`
(`Stacks.Curves.bridgePushoutSituation`).

The completed local ring of `Y` at the image `y` of `Spec k'` is computed as follows: writing
`k'' = ∏ k'_i` as a product of finite separable extensions of `k'`, it is the fibre product of the
product of the completed local rings of `X'` at the points of `C ∩ X'` and of `k'` over `∏ k'_i`.

## Main results

* `Stacks.Curves.subsingleton_primeSpectrum_of_isField` — the spectrum of a field has at most one
  point.
* `Stacks.Curves.isAffine_intersection_bridge` — `C ∩ X'` is affine.
* `Stacks.Curves.surjective_j_bridgePushoutSituation` — the collapse `C ∩ X' ⟶ Spec k'` is
  surjective.
* `Stacks.Curves.locallyOfFiniteType_pY_bridgePushoutSituation` — `Spec k'` is locally of finite
  type over `k`.
* `Stacks.Curves.isLocallyNoetherian_pushoutScheme_bridge` — `Y` is locally Noetherian.
* `Stacks.Curves.exists_isPullback_completedLocalRing_pushout_bridge` — the cartesian square
  describing the completed local ring of `Y` at `y`.

## References

* [Stacks Project, Tag 0E3M](https://stacks.math.columbia.edu/tag/0E3M)
* [Stacks Project, Tag 0E36](https://stacks.math.columbia.edu/tag/0E36)
* [Stacks Project, Tag 0E27](https://stacks.math.columbia.edu/tag/0E27)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Curves

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))]
  [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]

/-- The spectrum of a ring which is a field has at most one point. -/
@[ega "I 2.4.5" "at most one point"]
theorem subsingleton_primeSpectrum_of_isField {R : Type u} [CommRing R] (h : IsField R) :
    Subsingleton (PrimeSpectrum R) := by
  let := h.toField
  infer_instance

/-- The intersection of a rational bridge with the closure of its complement is affine. -/
theorem isAffine_intersection_bridge
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C) :
    IsAffine (intersectionWithComplementaryCurve C) :=
  isAffine_of_finiteType_of_dimension_zero k
    ((intersectionWithComplementaryCurveIdeal C).subschemeι ≫ (X ↘ Spec (.of k)))
    (topologicalKrullDim_intersection_bridge_eq_zero hdim hnodal hC)

/-- The spectrum of the global functions on a rational bridge has at most one point. -/
private theorem subsingleton_primeSpectrum_bridgeSections {K : Type u} [Field K] {Z : Scheme.{u}}
    [Z.Over (Spec (.of K))] [IsProper (Z ↘ Spec (.of K))] {C : Z.IdealSheafData}
    (hC : IsRationalBridge K Z C) : Subsingleton (PrimeSpectrum (Γ(C.subscheme, ⊤) : Type u)) :=
  have := hC.isIntegral
  subsingleton_primeSpectrum_of_isField
    (isField_of_universallyClosed K (C.subschemeι ≫ (Z ↘ Spec (.of K))))

/-- The collapse of the intersection of a rational bridge with the closure of its complement onto
`Spec k'` is surjective. -/
theorem surjective_j_bridgePushoutSituation
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C) :
    Surjective (bridgePushoutSituation hdim hnodal hC).j := by
  have := subsingleton_primeSpectrum_bridgeSections hC
  obtain ⟨w⟩ := nonempty_intersection_bridge hC
  refine ⟨fun y => ⟨w, ?_⟩⟩
  exact Subsingleton.elim (α := PrimeSpectrum (Γ(C.subscheme, ⊤) : Type u)) _ _

/-- The spectrum `Spec k'` of the global functions on a rational bridge is locally of finite type
over the base field. -/
theorem locallyOfFiniteType_pY_bridgePushoutSituation
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C) :
    LocallyOfFiniteType (bridgePushoutSituation hdim hnodal hC).pY := by
  let : Algebra k Γ(C.subscheme, ⊤) := (bridgeSectionsStructureMap C).hom.toAlgebra
  have : Module.Finite k Γ(C.subscheme, ⊤) :=
    Stacks.AlgebraicGeometry.ProperSectionsGeom.moduleFinite_globalSections_of_isProper k
      (C.subschemeι ≫ (X ↘ Spec (.of k)))
  change LocallyOfFiniteType (Spec.map (bridgeSectionsStructureMap (k := k) C))
  exact HasRingHomProperty.Spec_iff.mpr
    (inferInstanceAs (Algebra.FiniteType k Γ(C.subscheme, ⊤)))

/-- The contraction of a rational bridge is locally Noetherian. -/
theorem isLocallyNoetherian_pushoutScheme_bridge
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C) :
    IsLocallyNoetherian (pushoutScheme (bridgePushoutSituation hdim hnodal hC)) := by
  have : LocallyOfFiniteType (bridgePushoutSituation hdim hnodal hC).pY :=
    locallyOfFiniteType_pY_bridgePushoutSituation hdim hnodal hC
  have : IsLocallyNoetherian (bridgePushoutSituation hdim hnodal hC).S :=
    inferInstanceAs (IsLocallyNoetherian (Spec (.of k)))
  have : LocallyOfFiniteType (bridgePushoutSituation hdim hnodal hC).pX :=
    inferInstanceAs (LocallyOfFiniteType (complementaryCurveι C ≫ (X ↘ Spec (.of k))))
  have : LocallyOfFiniteType (bridgePushoutSituation hdim hnodal hC).pZ :=
    inferInstanceAs (LocallyOfFiniteType
      ((intersectionWithComplementaryCurveIdeal C).subschemeι ≫ (X ↘ Spec (.of k))))
  exact LocallyOfFiniteType.isLocallyNoetherian
    (pushoutToBase (bridgePushoutSituation hdim hnodal hC))

/-- The completed local ring of the contraction of a rational bridge. Writing
`k'' = Γ(C ∩ X', 𝒪)` as a product `∏ k'_i` of finite separable extensions of `k' = Γ(C, 𝒪_C)`,
there are a point `y` of the contraction `Y` and points `x'_i` of `X'` such that `y` is the image
of every point of `Spec k'`, each `x'_i` is the image of a point of `C ∩ X'`, each map
`𝒪^∧_{X', x'_i} ⟶ k'_i` is surjective, and the completed local ring of `Y` at `y` is the fibre
product of `∏ 𝒪^∧_{X', x'_i}` and `k'` over `∏ k'_i`. -/
theorem exists_isPullback_completedLocalRing_pushout_bridge
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C) :
    letI : IsIntegral C.subscheme := hC.isIntegral
    letI : Field Γ(C.subscheme, ⊤) :=
      (isField_of_universallyClosed k (C.subschemeι ≫ (X ↘ Spec (.of k)))).toField
    letI : Algebra Γ(C.subscheme, ⊤) Γ(intersectionWithComplementaryCurve C, ⊤) :=
      (Scheme.IdealSheafData.inclusion
        (le_sup_left : C ≤ intersectionWithComplementaryCurveIdeal C)).appTop.hom.toAlgebra
    ∃ (n : ℕ) (Ki : Fin n → Type u) (_ : ∀ i, Field (Ki i))
      (_ : ∀ i, Algebra (Γ(C.subscheme, ⊤) : Type u) (Ki i))
      (_ : ∀ i, Module.Finite (Γ(C.subscheme, ⊤) : Type u) (Ki i))
      (x' : Fin n → complementaryCurve C)
      (y : pushoutScheme (bridgePushoutSituation hdim hnodal hC))
      (bottomResidueMap :
        Scheme.completedLocalRing (pushoutScheme (bridgePushoutSituation hdim hnodal hC)) y →+*
          (Γ(C.subscheme, ⊤) : Type u))
      (completionMap :
        Scheme.completedLocalRing (pushoutScheme (bridgePushoutSituation hdim hnodal hC)) y →+*
          (∀ i, Scheme.completedLocalRing (complementaryCurve C) (x' i)))
      (componentResidueMap :
        ∀ i, Scheme.completedLocalRing (complementaryCurve C) (x' i) →+* Ki i),
      Nonempty (Γ(intersectionWithComplementaryCurve C, ⊤) ≃ₐ[(Γ(C.subscheme, ⊤) : Type u)]
          (∀ i, Ki i)) ∧
        (∀ p : (bridgePushoutSituation hdim hnodal hC).Y,
          pushoutInr (bridgePushoutSituation hdim hnodal hC) p = y) ∧
        (∀ i, ∃ w : intersectionWithComplementaryCurve C,
          x' i = (Scheme.IdealSheafData.inclusion
            (le_sup_right : complementaryCurveIdeal C ≤
              intersectionWithComplementaryCurveIdeal C)).base w) ∧
        (∀ i, Function.Surjective (componentResidueMap i)) ∧
        IsPullback (CommRingCat.ofHom bottomResidueMap) (CommRingCat.ofHom completionMap)
          (CommRingCat.ofHom
            (RingHom.pi fun i => algebraMap (Γ(C.subscheme, ⊤) : Type u) (Ki i)))
          (CommRingCat.ofHom
            (RingHom.pi fun i => (componentResidueMap i).comp (Pi.evalRingHom _ i))) := by
  let : IsIntegral C.subscheme := hC.isIntegral
  let : Field Γ(C.subscheme, ⊤) :=
    (isField_of_universallyClosed k (C.subschemeι ≫ (X ↘ Spec (.of k)))).toField
  let : Algebra k Γ(C.subscheme, ⊤) := (bridgeSectionsStructureMap C).hom.toAlgebra
  let : Algebra k Γ(intersectionWithComplementaryCurve C, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫
      ((intersectionWithComplementaryCurveIdeal C).subschemeι ≫
        (X ↘ Spec (.of k))).appTop).hom.toAlgebra
  let : Algebra Γ(C.subscheme, ⊤) Γ(intersectionWithComplementaryCurve C, ⊤) :=
    (Scheme.IdealSheafData.inclusion
      (le_sup_left : C ≤ intersectionWithComplementaryCurveIdeal C)).appTop.hom.toAlgebra
  have := isScalarTower_bridgeSections_intersectionSections (k := k) (X := X) hC.isIntegral
  obtain ⟨hetale, hfinite⟩ := etale_intersectionSections_bridge hdim hnodal hC
  obtain ⟨n, Ki, hKifield, hKialg, hKifin, hKisep, hrk, ⟨eAlg⟩⟩ :=
    exists_fin_algEquiv_pi_of_etale k (Γ(C.subscheme, ⊤) : Type u)
      (Γ(intersectionWithComplementaryCurve C, ⊤) : Type u)
  have : IsAffine (intersectionWithComplementaryCurve C) :=
    isAffine_intersection_bridge hdim hnodal hC
  have : IsLocallyNoetherian (pushoutScheme (bridgePushoutSituation hdim hnodal hC)) :=
    isLocallyNoetherian_pushoutScheme_bridge hdim hnodal hC
  have : Surjective (bridgePushoutSituation hdim hnodal hC).j :=
    surjective_j_bridgePushoutSituation hdim hnodal hC
  let ε : Γ(intersectionWithComplementaryCurve C, ⊤) ≅ CommRingCat.of (∀ i, Ki i) :=
    eAlg.toRingEquiv.toCommRingCatIso
  let eZ : intersectionWithComplementaryCurve C ≅ Spec (.of (∀ i, Ki i)) :=
    (intersectionWithComplementaryCurve C).isoSpec ≪≫ asIso (Spec.map ε.inv)
  have hpi : CommRingCat.ofHom
        (RingHom.pi fun i => algebraMap (Γ(C.subscheme, ⊤) : Type u) (Ki i)) ≫ ε.inv =
      (Scheme.IdealSheafData.inclusion
        (le_sup_left : C ≤ intersectionWithComplementaryCurveIdeal C)).appTop := by
    ext c
    change eAlg.symm (algebraMap (Γ(C.subscheme, ⊤) : Type u) (∀ i, Ki i) c) = _
    rw [eAlg.symm.commutes, RingHom.algebraMap_toAlgebra]
  have hjaux : (Scheme.IdealSheafData.inclusion
        (le_sup_left : C ≤ intersectionWithComplementaryCurveIdeal C) ≫
        C.subscheme.toSpecΓ) =
      eZ.hom ≫ Spec.map (CommRingCat.ofHom
        (RingHom.pi fun i => algebraMap (Γ(C.subscheme, ⊤) : Type u) (Ki i))) := by
    simp only [eZ, Iso.trans_hom, Scheme.isoSpec_hom, asIso_hom]
    rw [Category.assoc, ← Spec.map_comp, hpi]
    exact Scheme.toSpecΓ_naturality _
  have hj : (bridgePushoutSituation hdim hnodal hC).j = eZ.hom ≫
      Spec.map (CommRingCat.ofHom
        (RingHom.pi fun i => algebraMap (Γ(C.subscheme, ⊤) : Type u) (Ki i))) ≫
      (Iso.refl (Spec (.of (Γ(C.subscheme, ⊤) : Type u)))).inv := by
    rw [Iso.refl_inv, Category.comp_id]
    exact hjaux
  obtain ⟨hx, completionMap, bottomResidueMap, componentResidueMap, -, -, hcomp, hpb⟩ :=
    exists_pushoutCompletedLocalRing_isPullback (bridgePushoutSituation hdim hnodal hC) n
      (Γ(C.subscheme, ⊤) : Type u) Ki eZ (Iso.refl _) hj
  have := subsingleton_primeSpectrum_bridgeSections hC
  have hsurjStalk : ∀ i, Function.Surjective (Scheme.stalkClosedPointTo
      ((Spec.map (CommRingCat.ofHom (Pi.evalRingHom Ki i)) ≫ eZ.inv) ≫
        (bridgePushoutSituation hdim hnodal hC).i)).hom := by
    intro i
    have hspec : IsClosedImmersion (Spec.map (CommRingCat.ofHom (Pi.evalRingHom Ki i))) :=
      IsClosedImmersion.spec_of_surjective _ fun x =>
        ⟨Function.update 0 i x, by simp⟩
    have hinv : IsIso eZ.inv := ⟨eZ.hom, eZ.inv_hom_id, eZ.hom_inv_id⟩
    have hcinv : IsClosedImmersion eZ.inv := inferInstance
    have hpoint : IsClosedImmersion
        (Spec.map (CommRingCat.ofHom (Pi.evalRingHom Ki i)) ≫ eZ.inv) :=
      @IsClosedImmersion.comp _ _ _ _ _ hspec hcinv
    have hsi : IsClosedImmersion (bridgePushoutSituation hdim hnodal hC).i :=
      (bridgePushoutSituation hdim hnodal hC).isClosedImmersion_i
    have : IsClosedImmersion
        ((Spec.map (CommRingCat.ofHom (Pi.evalRingHom Ki i)) ≫ eZ.inv) ≫
          (bridgePushoutSituation hdim hnodal hC).i) :=
      @IsClosedImmersion.comp _ _ _ _ _ hpoint hsi
    exact ((ConcreteCategory.bijective_of_isIso
      (stalkClosedPointIso (CommRingCat.of (Ki i))).hom).2).comp
      (Scheme.Hom.stalkMap_surjective _ _)
  refine ⟨n, Ki, hKifield, hKialg, hKifin, _, _, bottomResidueMap, completionMap,
    componentResidueMap, ⟨eAlg⟩, fun p => ?_, fun i => ⟨_, rfl⟩, fun i x => ?_, hpb⟩
  · exact congrArg (pushoutInr (bridgePushoutSituation hdim hnodal hC))
      (Subsingleton.elim (α := PrimeSpectrum (Γ(C.subscheme, ⊤) : Type u)) _ _)
  · obtain ⟨a, ha⟩ := hsurjStalk i x
    exact ⟨_, (DFunLike.congr_fun (hcomp i) a).trans ha⟩

end Stacks.Curves

end
