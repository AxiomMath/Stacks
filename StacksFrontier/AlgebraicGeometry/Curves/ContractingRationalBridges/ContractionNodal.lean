module

public import StacksFrontier.AlgebraicGeometry.Curves.CanonicalContraction.NodalAwayFromAttaching
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.ComplementaryNodal
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.ContractionTarget
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.PushoutCompletionShape
public import StacksFrontier.AlgebraicGeometry.Curves.Node.AlgebraCompletion
public import StacksFrontier.AlgebraicGeometry.Curves.Node.ConstantCoeffInBase
public import StacksFrontier.AlgebraicGeometry.Curves.NodeNodalAlgebraAscent
public import StacksFrontier.AlgebraicGeometry.Curves.NodeResidueFieldSeparable
public import StacksFrontier.AlgebraicGeometry.Curves.NodeWitnesses
public import StacksFrontier.AlgebraicGeometry.Pushout.FiniteType
public import StacksFrontier.AlgebraicGeometry.Pushout.SquareSections
public import StacksFrontier.AlgebraicGeometry.Pushout.TopologicalRestriction
public import StacksFrontier.RingTheory.DiscreteValuationRing.FormallySmoothExtension
public import StacksCore.Tactic.StacksAttribute
import all StacksFrontier.AlgebraicGeometry.Curves.Node.Algebra

/-!
# The contraction of a rational bridge has at-worst-nodal singularities

Let `k` be a field, let `X` be a proper scheme over `k` of dimension one with `H⁰(X, 𝒪_X) = k`
and at-worst-nodal singularities, and let `C ⊆ X` be a rational bridge. Write `X'` for the
scheme-theoretic closure of `X \ C`, `k' = Γ(C, 𝒪_C)` and `k'' = Γ(C ∩ X', 𝒪)`, and let `Y` be the
pushout `AlgebraicGeometry.pushoutScheme` of `C ∩ X' ⟶ X'` along the collapse `C ∩ X' ⟶ Spec k'`,
over `k` by `AlgebraicGeometry.pushoutToBase`. The singularities of `Y` are at-worst-nodal.

## Main results

* `Stacks.Curves.locallyOfFiniteType_pushoutToBase_bridge`: `Y` is locally of finite type over
  `k`.
* `Stacks.Curves.topologicalKrullDim_pushoutScheme_bridge`: `Y` has dimension one.
* `Stacks.Curves.isNode_pushoutScheme_bridge`: the image `y` of `Spec k' ⟶ Y` is a node of `Y`.
* `Stacks.Curves.smoothAt_or_isNode_pushoutScheme_bridge_of_ne`: every other closed point of `Y`
  is a smooth point of `Y` over `k` or a node.
* `Stacks.Curves.hasAtWorstNodalSingularities_pushoutScheme_bridge`: the singularities of `Y` are
  at-worst-nodal.

## References

* [Stacks Project, Tag 0E3M](https://stacks.math.columbia.edu/tag/0E3M)
* [Stacks Project, Tag 0E25](https://stacks.math.columbia.edu/tag/0E25)
* [Stacks Project, Tag 0E27](https://stacks.math.columbia.edu/tag/0E27)
* [Stacks Project, Tag 0C4A](https://stacks.math.columbia.edu/tag/0C4A)
* [Stacks Project, Tag 0C4D](https://stacks.math.columbia.edu/tag/0C4D)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Curves

variable {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
  [IsProper (X ↘ Spec (.of k))]
  [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]

/-- The contraction of a rational bridge is locally of finite type over the base field. -/
theorem locallyOfFiniteType_pushoutToBase_bridge
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C) :
    LocallyOfFiniteType (pushoutToBase (bridgePushoutSituation hdim hnodal hC)) := by
  have : IsLocallyNoetherian (bridgePushoutSituation hdim hnodal hC).S :=
    inferInstanceAs (IsLocallyNoetherian (Spec (.of k)))
  have : LocallyOfFiniteType (bridgePushoutSituation hdim hnodal hC).pY :=
    locallyOfFiniteType_pY_bridgePushoutSituation hdim hnodal hC
  have : LocallyOfFiniteType (bridgePushoutSituation hdim hnodal hC).pX :=
    inferInstanceAs (LocallyOfFiniteType (complementaryCurveι C ≫ (X ↘ Spec (.of k))))
  have : LocallyOfFiniteType (bridgePushoutSituation hdim hnodal hC).pZ :=
    inferInstanceAs (LocallyOfFiniteType
      ((intersectionWithComplementaryCurveIdeal C).subschemeι ≫ (X ↘ Spec (.of k))))
  infer_instance

/-- The contraction of a rational bridge is one-dimensional. -/
theorem topologicalKrullDim_pushoutScheme_bridge
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C) :
    topologicalKrullDim (pushoutScheme (bridgePushoutSituation hdim hnodal hC)) = 1 := by
  have hc := (exists_contraction_pushoutScheme_bridge hdim hnodal hC).choose_spec
  obtain ⟨g, -, -, hdimY, -⟩ :=
    exists_isProper_structureMorphism_contraction_bridge hdim hnodal hc
  exact hdimY

/-- The canonical map `X' ⟶ Y` of the pushout is a morphism over the base field: composed with
the structure morphism of the pushout it is the structure morphism of `X'`. -/
theorem pushoutInl_comp_pushoutToBase_bridge
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C) :
    pushoutInl (bridgePushoutSituation hdim hnodal hC) ≫
        pushoutToBase (bridgePushoutSituation hdim hnodal hC) =
      complementaryCurveι C ≫ (X ↘ Spec (.of k)) := by
  rw [show pushoutInl (bridgePushoutSituation hdim hnodal hC) ≫
      pushoutToBase (bridgePushoutSituation hdim hnodal hC) =
      (bridgePushoutSituation hdim hnodal hC).pX from by simp [pushoutToBase]]
  rfl

/-- The image `y` of `Spec k' ⟶ Y` is also the image of a point of `X'` lying over the
bridge `C`. -/
theorem exists_mem_complementaryCurve_pushoutInl_eq_bridge
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C)
    {y : pushoutScheme (bridgePushoutSituation hdim hnodal hC)}
    (hy : ∀ p : (bridgePushoutSituation hdim hnodal hC).Y,
      pushoutInr (bridgePushoutSituation hdim hnodal hC) p = y) :
    ∃ z : complementaryCurve C,
      pushoutInl (bridgePushoutSituation hdim hnodal hC) z = y ∧
        (complementaryCurveι C).base z ∈ (C.support : Set X) := by
  obtain ⟨w⟩ := nonempty_intersection_bridge hC
  set s := bridgePushoutSituation hdim hnodal hC with hs
  have hiw : s.i w = (Scheme.IdealSheafData.inclusion
      (le_sup_right : complementaryCurveIdeal C ≤
        intersectionWithComplementaryCurveIdeal C)).base w := rfl
  refine ⟨s.i w, ?_, ?_⟩
  · have hsq := (pushoutAlongClosedImmersionAndIntegral s).isPushout.w
    have hkey : pushoutInl s (s.i w) = pushoutInr s (s.j w) :=
      congrArg (fun f : s.Z ⟶ pushoutScheme s => f.base w) hsq
    rw [hkey, hy]
  · have hwmem : (intersectionWithComplementaryCurveIdeal C).subschemeι.base w ∈
        ((intersectionWithComplementaryCurveIdeal C).support : Set X) := by
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨w, rfl⟩
    obtain ⟨hwC, -⟩ :=
      mem_support_and_mem_support_complementaryCurveIdeal_of_mem_intersection hwmem
    rw [hiw, Stacks.Chow.inclusion_subschemeι_base
      (le_sup_right : complementaryCurveIdeal C ≤
        intersectionWithComplementaryCurveIdeal C) w]
    exact hwC

/-- For a point `z` of `X'` lying over the bridge `C`, the residue field of the contraction `Y` at
the image of `z` is separable over the base field. -/
theorem isSeparableExtension_residueField_pushoutScheme_bridge
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C)
    (z : complementaryCurve C)
    (hz : (complementaryCurveι C).base z ∈ (C.support : Set X)) :
    letI : Algebra k ((pushoutScheme (bridgePushoutSituation hdim hnodal hC)).residueField
        (pushoutInl (bridgePushoutSituation hdim hnodal hC) z)) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫
        (pushoutToBase (bridgePushoutSituation hdim hnodal hC)).appTop ≫
          (pushoutScheme (bridgePushoutSituation hdim hnodal hC)).Γevaluation
            (pushoutInl (bridgePushoutSituation hdim hnodal hC) z)).hom.toAlgebra
    Algebra.IsSeparableExtension k
      ((pushoutScheme (bridgePushoutSituation hdim hnodal hC)).residueField
        (pushoutInl (bridgePushoutSituation hdim hnodal hC) z)) := by
  let algP : Algebra k ((pushoutScheme (bridgePushoutSituation hdim hnodal hC)).residueField
      (pushoutInl (bridgePushoutSituation hdim hnodal hC) z)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫
      (pushoutToBase (bridgePushoutSituation hdim hnodal hC)).appTop ≫
        (pushoutScheme (bridgePushoutSituation hdim hnodal hC)).Γevaluation
          (pushoutInl (bridgePushoutSituation hdim hnodal hC) z)).hom.toAlgebra
  let algX' : Algebra k ((complementaryCurve C).residueField z) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫
      (complementaryCurveι C ≫ (X ↘ Spec (.of k))).appTop ≫
        (complementaryCurve C).Γevaluation z).hom.toAlgebra
  have : Algebra.IsSeparableExtension k ((complementaryCurve C).residueField z) :=
    isSeparableExtension_residueField_complementaryCurve_bridge hdim hnodal hC z hz
  have h2 : (complementaryCurveι C ≫ (X ↘ Spec (.of k))).appTop =
      (pushoutToBase (bridgePushoutSituation hdim hnodal hC)).appTop ≫
      (pushoutInl (bridgePushoutSituation hdim hnodal hC)).appTop := by
    rw [← Scheme.Hom.comp_appTop, pushoutInl_comp_pushoutToBase_bridge hdim hnodal hC]
    rfl
  have f : ↥((pushoutScheme (bridgePushoutSituation hdim hnodal hC)).residueField
        (pushoutInl (bridgePushoutSituation hdim hnodal hC) z)) →ₐ[k]
      ↥((complementaryCurve C).residueField z) :=
    { __ := ((pushoutInl (bridgePushoutSituation hdim hnodal hC)).residueFieldMap z).hom
      commutes' := fun r => by
        simp only [algP, algX', RingHom.algebraMap_toAlgebra, h2, CommRingCat.hom_comp,
          RingHom.coe_comp, Function.comp_apply]
        exact Scheme.Γevaluation_naturality_apply
          (pushoutInl (bridgePushoutSituation hdim hnodal hC)) z _ }
  exact IsDiscreteValuationRing.isSeparableExtension_of_algHom f

/-- The pushout situation of a rational bridge has a unique point `Spec k' ⟶ Y`. -/
private theorem exists_forall_eq_bridgePushoutSituation_Y
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C) :
    ∃ p₀ : (bridgePushoutSituation hdim hnodal hC).Y, ∀ p, p = p₀ := by
  let : IsIntegral C.subscheme := hC.isIntegral
  let : Field Γ(C.subscheme, ⊤) :=
    (isField_of_universallyClosed k (C.subschemeι ≫ (X ↘ Spec (.of k)))).toField
  have : Unique (PrimeSpectrum (Γ(C.subscheme, ⊤) : Type u)) := PrimeSpectrum.instUnique
  exact ⟨(default : PrimeSpectrum (Γ(C.subscheme, ⊤) : Type u)),
    Unique.eq_default (α := PrimeSpectrum (Γ(C.subscheme, ⊤) : Type u))⟩

/-- The image `y` of `Spec k' ⟶ Y` is a node of the contraction `Y` of a rational bridge. -/
theorem isNode_pushoutScheme_bridge
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C)
    (y : pushoutScheme (bridgePushoutSituation hdim hnodal hC))
    (hy : ∀ p : (bridgePushoutSituation hdim hnodal hC).Y,
      pushoutInr (bridgePushoutSituation hdim hnodal hC) p = y) :
    letI : (pushoutScheme (bridgePushoutSituation hdim hnodal hC)).Over (Spec (.of k)) :=
      ⟨pushoutToBase (bridgePushoutSituation hdim hnodal hC)⟩
    IsNode k (pushoutScheme (bridgePushoutSituation hdim hnodal hC)) y := by
  let : IsIntegral C.subscheme := hC.isIntegral
  let : Field Γ(C.subscheme, ⊤) :=
    (isField_of_universallyClosed k (C.subschemeι ≫ (X ↘ Spec (.of k)))).toField
  let : Algebra Γ(C.subscheme, ⊤) Γ(intersectionWithComplementaryCurve C, ⊤) :=
    (Scheme.IdealSheafData.inclusion
      (le_sup_left : C ≤ intersectionWithComplementaryCurveIdeal C)).appTop.hom.toAlgebra
  let : (pushoutScheme (bridgePushoutSituation hdim hnodal hC)).Over (Spec (.of k)) :=
    ⟨pushoutToBase (bridgePushoutSituation hdim hnodal hC)⟩
  have : LocallyOfFiniteType
      (pushoutScheme (bridgePushoutSituation hdim hnodal hC) ↘ Spec (.of k)) :=
    locallyOfFiniteType_pushoutToBase_bridge hdim hnodal hC
  have : IsLocallyNoetherian (pushoutScheme (bridgePushoutSituation hdim hnodal hC)) :=
    isLocallyNoetherian_pushoutScheme_bridge hdim hnodal hC
  obtain ⟨y', hy', hgen, hsplit⟩ :=
    exists_ringEquiv_completedLocalRing_contraction_bridge k X hdim hnodal C hC
  obtain ⟨p₀, -⟩ := exists_forall_eq_bridgePushoutSituation_Y hdim hnodal hC
  have hyy : y' = y := (hy' p₀).symm.trans (hy p₀)
  subst hyy
  obtain ⟨z, hzy, hz⟩ := exists_mem_complementaryCurve_pushoutInl_eq_bridge hdim hnodal hC hy
  subst hzy
  have : IsLocalRing (Scheme.completedLocalRing
      (pushoutScheme (bridgePushoutSituation hdim hnodal hC))
      (pushoutInl (bridgePushoutSituation hdim hnodal hC) z)) :=
    Scheme.completedLocalRing_isLocal _ _
  have : IsNoetherianRing (Scheme.completedLocalRing
      (pushoutScheme (bridgePushoutSituation hdim hnodal hC))
      (pushoutInl (bridgePushoutSituation hdim hnodal hC) z)) :=
    Scheme.completedLocalRing_isNoetherian _ _
  obtain ⟨e⟩ := hgen
  have : IsNoetherianRing ↥(PowerSeries.constantCoeffInBase
      (Γ(C.subscheme, ⊤) : Type u) (Γ(intersectionWithComplementaryCurve C, ⊤) : Type u)) :=
    isNoetherianRing_of_surjective _ _ e.toRingHom e.surjective
  have hkey : IsReduced (Scheme.completedLocalRing
        (pushoutScheme (bridgePushoutSituation hdim hnodal hC))
        (pushoutInl (bridgePushoutSituation hdim hnodal hC) z)) ∧
      HasNodalQuadraticRelation (Scheme.completedLocalRing
        (pushoutScheme (bridgePushoutSituation hdim hnodal hC))
        (pushoutInl (bridgePushoutSituation hdim hnodal hC) z)) := by
    rcases isField_and_isSeparable_or_algEquiv_prod_intersectionSections_bridge k X hdim hnodal
      C hC with ⟨hfield, hrank, hsep⟩ | hprod
    · let : Field (Γ(intersectionWithComplementaryCurve C, ⊤) : Type u) := hfield.toField
      have := hsep
      refine ⟨isReduced_of_injective e.toRingHom e.injective, ?_⟩
      exact hasNodalQuadraticRelation_of_ringEquiv e.symm
        (hasNodalQuadraticRelation_constantCoeffInBase_of_isSeparable
          (Γ(C.subscheme, ⊤) : Type u) (Γ(intersectionWithComplementaryCurve C, ⊤) : Type u)
          hrank)
    · obtain ⟨e₂⟩ := hsplit hprod
      have : IsNoetherianRing (nodeAlgebra (Γ(C.subscheme, ⊤) : Type u)) :=
        (isNagataRing_nodeAlgebra (Γ(C.subscheme, ⊤) : Type u)).1
      have : _root_.IsReduced (nodeAlgebra (Γ(C.subscheme, ⊤) : Type u)) :=
        isReduced_nodeAlgebra (Γ(C.subscheme, ⊤) : Type u)
      refine ⟨isReduced_of_injective e₂.toRingHom e₂.injective, ?_⟩
      exact hasNodalQuadraticRelation_of_ringEquiv e₂.symm
        (hasNodalQuadraticRelation_nodeAlgebra (Γ(C.subscheme, ⊤) : Type u))
  let : Algebra k ((pushoutScheme (bridgePushoutSituation hdim hnodal hC)).presheaf.stalk
      (pushoutInl (bridgePushoutSituation hdim hnodal hC) z)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫
      (pushoutScheme (bridgePushoutSituation hdim hnodal hC) ↘ Spec (.of k)).appTop ≫
      (pushoutScheme (bridgePushoutSituation hdim hnodal hC)).presheaf.germ ⊤
        (pushoutInl (bridgePushoutSituation hdim hnodal hC) z) trivial).hom.toAlgebra
  refine isNode_of_isNodalAlgebra_stalk k (pushoutScheme (bridgePushoutSituation hdim hnodal hC))
    (topologicalKrullDim_pushoutScheme_bridge hdim hnodal hC) _ ?_
  change IsNodalAlgebra k ((pushoutScheme (bridgePushoutSituation hdim hnodal hC)).presheaf.stalk
    (pushoutInl (bridgePushoutSituation hdim hnodal hC) z))
  refine isNodalAlgebra_of_isNodalAlgebra_adicCompletion k _ ⟨?_, hkey.1, hkey.2⟩
  exact isSeparableExtension_of_algEquiv (residueFieldAlgEquiv_adicCompletion k _)
    (isSeparableExtension_residueField_pushoutScheme_bridge hdim hnodal hC z hz)

/-- The image `y` of `Spec k' ⟶ Y` is a closed point of `Y`. -/
theorem isClosed_singleton_pushoutInr_image_bridge
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C)
    (y : pushoutScheme (bridgePushoutSituation hdim hnodal hC))
    (hy : ∀ p : (bridgePushoutSituation hdim hnodal hC).Y,
      pushoutInr (bridgePushoutSituation hdim hnodal hC) p = y) :
    IsClosed ({y} : Set (pushoutScheme (bridgePushoutSituation hdim hnodal hC))) := by
  obtain ⟨p₀, -⟩ := exists_forall_eq_bridgePushoutSituation_Y hdim hnodal hC
  have hmem : y ∈ Set.range (pushoutInr (bridgePushoutSituation hdim hnodal hC)).base :=
    ⟨p₀, hy p₀⟩
  have hyrange : Set.range (pushoutInr (bridgePushoutSituation hdim hnodal hC)).base = {y} := by
    refine Set.eq_singleton_iff_unique_mem.mpr ⟨hmem, ?_⟩
    rintro x ⟨p, rfl⟩
    exact hy p
  rw [← hyrange]
  exact (pushoutInr (bridgePushoutSituation hdim hnodal hC)).isClosedEmbedding.isClosed_range

/-- At a closed point `w` other than the image `y` of `Spec k'`, the contraction `Y` of a rational
bridge is smooth over the base field or has a node. -/
theorem smoothAt_or_isNode_pushoutScheme_bridge_of_ne
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C)
    (y : pushoutScheme (bridgePushoutSituation hdim hnodal hC))
    (hy : ∀ p : (bridgePushoutSituation hdim hnodal hC).Y,
      pushoutInr (bridgePushoutSituation hdim hnodal hC) p = y)
    (w : pushoutScheme (bridgePushoutSituation hdim hnodal hC))
    (hwclosed : IsClosed ({w} : Set (pushoutScheme (bridgePushoutSituation hdim hnodal hC))))
    (hwy : w ≠ y) :
    letI : (pushoutScheme (bridgePushoutSituation hdim hnodal hC)).Over (Spec (.of k)) :=
      ⟨pushoutToBase (bridgePushoutSituation hdim hnodal hC)⟩
    InfinitesimalLifting.SmoothAt (pushoutToBase (bridgePushoutSituation hdim hnodal hC)) w ∨
      IsNode k (pushoutScheme (bridgePushoutSituation hdim hnodal hC)) w := by
  let : (pushoutScheme (bridgePushoutSituation hdim hnodal hC)).Over (Spec (.of k)) :=
    ⟨pushoutToBase (bridgePushoutSituation hdim hnodal hC)⟩
  have hlft : LocallyOfFiniteType
      (pushoutScheme (bridgePushoutSituation hdim hnodal hC) ↘ Spec (.of k)) :=
    locallyOfFiniteType_pushoutToBase_bridge hdim hnodal hC
  have hlft' : @LocallyOfFiniteType (pushoutScheme (bridgePushoutSituation hdim hnodal hC))
      (Spec (.of k)) (pushoutToBase (bridgePushoutSituation hdim hnodal hC)) :=
    locallyOfFiniteType_pushoutToBase_bridge hdim hnodal hC
  have hyclosed := isClosed_singleton_pushoutInr_image_bridge hdim hnodal hC y hy
  set W : (pushoutScheme (bridgePushoutSituation hdim hnodal hC)).Opens :=
    ⟨{y}ᶜ, hyclosed.isOpen_compl⟩ with hWdef
  have hWbot : pushoutInr (bridgePushoutSituation hdim hnodal hC) ⁻¹ᵁ W = ⊥ :=
    TopologicalSpace.Opens.ext (Set.eq_empty_iff_forall_notMem.mpr fun p hp => hp (hy p))
  have hiso : IsIso (pushoutInl (bridgePushoutSituation hdim hnodal hC) ∣_ W) :=
    pushoutInl_isIso_morphismRestrict _ W hWbot
  have hwW : w ∈ W := hwy
  obtain ⟨u, hu⟩ := (Scheme.Hom.homeomorph
    (pushoutInl (bridgePushoutSituation hdim hnodal hC) ∣_ W)).surjective ⟨w, hwW⟩
  have hetaleι : @Etale (pushoutInl (bridgePushoutSituation hdim hnodal hC) ⁻¹ᵁ W).toScheme
      (complementaryCurve C) (pushoutInl (bridgePushoutSituation hdim hnodal hC) ⁻¹ᵁ W).ι :=
    inferInstanceAs (@Etale _ (bridgePushoutSituation hdim hnodal hC).X
      (pushoutInl (bridgePushoutSituation hdim hnodal hC) ⁻¹ᵁ W).ι)
  have hetale : Etale ((pushoutInl (bridgePushoutSituation hdim hnodal hC) ⁻¹ᵁ W).ι ≫
      pushoutInl (bridgePushoutSituation hdim hnodal hC)) := by
    rw [← morphismRestrict_ι (pushoutInl (bridgePushoutSituation hdim hnodal hC)) W]
    infer_instance
  have hbu : ((pushoutInl (bridgePushoutSituation hdim hnodal hC) ⁻¹ᵁ W).ι ≫
      pushoutInl (bridgePushoutSituation hdim hnodal hC)).base u = w := by
    have h := congrArg (fun f : (pushoutInl (bridgePushoutSituation hdim hnodal hC)
        ⁻¹ᵁ W).toScheme ⟶
        pushoutScheme (bridgePushoutSituation hdim hnodal hC) => f.base u)
      (morphismRestrict_ι (pushoutInl (bridgePushoutSituation hdim hnodal hC)) W)
    rw [← h]
    change W.ι.base ((pushoutInl (bridgePushoutSituation hdim hnodal hC) ∣_ W).base u) = w
    rw [show (pushoutInl (bridgePushoutSituation hdim hnodal hC) ∣_ W).base u =
      (⟨w, hwW⟩ : W.toScheme) from hu]
    rfl
  have hcomm : ((pushoutInl (bridgePushoutSituation hdim hnodal hC) ⁻¹ᵁ W).ι ≫
        pushoutInl (bridgePushoutSituation hdim hnodal hC)) ≫
        pushoutToBase (bridgePushoutSituation hdim hnodal hC) =
      (pushoutInl (bridgePushoutSituation hdim hnodal hC) ⁻¹ᵁ W).ι ≫
        (complementaryCurveι C ≫ (X ↘ Spec (.of k))) := by
    rw [Category.assoc, pushoutInl_comp_pushoutToBase_bridge hdim hnodal hC]
    rfl
  have huclosed : IsClosed ({u} :
      Set (pushoutInl (bridgePushoutSituation hdim hnodal hC) ⁻¹ᵁ W).toScheme) :=
    (isClosed_singleton_iff_of_etale
      (pushoutToBase (bridgePushoutSituation hdim hnodal hC))
      ((pushoutInl (bridgePushoutSituation hdim hnodal hC) ⁻¹ᵁ W).ι ≫
        pushoutInl (bridgePushoutSituation hdim hnodal hC)) u).mp
      (by rw [hbu]; exact hwclosed)
  have hxclosed : IsClosed ({((pushoutInl (bridgePushoutSituation hdim hnodal hC) ⁻¹ᵁ W).ι).base u}
      : Set (complementaryCurve C)) :=
    (isClosed_singleton_iff_of_etale (complementaryCurveι C ≫ (X ↘ Spec (.of k)))
      (pushoutInl (bridgePushoutSituation hdim hnodal hC) ⁻¹ᵁ W).ι u).mpr huclosed
  have hX' := hasAtWorstNodalSingularities_complementaryCurve_bridge hdim hnodal hC
    (((pushoutInl (bridgePushoutSituation hdim hnodal hC) ⁻¹ᵁ W).ι).base u) hxclosed
  have hconcl := smoothAt_or_isNode_of_etale_of_comm k
    (complementaryCurveι C ≫ (X ↘ Spec (.of k)))
    (pushoutToBase (bridgePushoutSituation hdim hnodal hC))
    (topologicalKrullDim_complementaryCurve_eq_one
      (equidimensional_of_isIso_globalSections_of_dimension_one k (X ↘ Spec (.of k)) hdim)
      hdim hnodal C hC.complementaryCurve_nonempty)
    (topologicalKrullDim_pushoutScheme_bridge hdim hnodal hC)
    (pushoutInl (bridgePushoutSituation hdim hnodal hC) ⁻¹ᵁ W).ι
    ((pushoutInl (bridgePushoutSituation hdim hnodal hC) ⁻¹ᵁ W).ι ≫
      pushoutInl (bridgePushoutSituation hdim hnodal hC))
    hcomm u hX'
  rwa [hbu] at hconcl

/-- The singularities of the contraction `Y` of a rational bridge, the pushout
`AlgebraicGeometry.pushoutScheme` of `Stacks.Curves.bridgePushoutSituation` over `k` by
`AlgebraicGeometry.pushoutToBase`, are at-worst-nodal. -/
@[stacks 0E3M "the singularities of Y are at-worst-nodal"]
theorem hasAtWorstNodalSingularities_pushoutScheme_bridge
    (hdim : topologicalKrullDim X = 1)
    (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C) :
    letI : (pushoutScheme (bridgePushoutSituation hdim hnodal hC)).Over (Spec (.of k)) :=
      ⟨pushoutToBase (bridgePushoutSituation hdim hnodal hC)⟩
    HasAtWorstNodalSingularities k (pushoutScheme (bridgePushoutSituation hdim hnodal hC)) := by
  let : (pushoutScheme (bridgePushoutSituation hdim hnodal hC)).Over (Spec (.of k)) :=
    ⟨pushoutToBase (bridgePushoutSituation hdim hnodal hC)⟩
  obtain ⟨p₀, hp₀⟩ := exists_forall_eq_bridgePushoutSituation_Y hdim hnodal hC
  have hy : ∀ p : (bridgePushoutSituation hdim hnodal hC).Y,
      pushoutInr (bridgePushoutSituation hdim hnodal hC) p =
      pushoutInr (bridgePushoutSituation hdim hnodal hC) p₀ :=
    fun p => by rw [hp₀ p]
  intro w hw
  by_cases hwy : w = pushoutInr (bridgePushoutSituation hdim hnodal hC) p₀
  · subst hwy
    exact Or.inr (isNode_pushoutScheme_bridge hdim hnodal hC _ hy)
  · exact smoothAt_or_isNode_pushoutScheme_bridge_of_ne hdim hnodal hC _ hy w hw hwy

end Stacks.Curves

end
