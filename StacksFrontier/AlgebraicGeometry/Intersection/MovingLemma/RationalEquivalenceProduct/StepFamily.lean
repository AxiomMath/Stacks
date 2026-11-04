module

public import
  StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.RationalEquivalenceProduct.StepCone
public import StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.MovingFamilyChowModel
public import
  StacksFrontier.AlgebraicGeometry.Intersection.MovingLemma.RationalEquivalenceProduct.Sections
public import StacksFrontier.AlgebraicGeometry.Chow.FamilyFibreDivisors.FibreDeltaDimensionEq
public import StacksFrontier.AlgebraicGeometry.Chow.GysinTrivialRestriction
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ModuleComposition

/-!
# Tag 0B1V: the family moving the cone

For the cone `C ⊆ 𝐏(V)` of Tag 0B0E, Tag 0B1T supplies a closed subvariety `C' ⊆ 𝐏(V) × ℙ¹`
dominating `ℙ¹` with `C'_0 = C`, meeting `X × ℙ¹` properly and with `C'_∞` meeting the given
`T_i` properly. This file records the dimension of `C'` and of `C'_∞`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Chow AlgebraicGeometry.TorFormula AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

namespace Stacks.Intersection.RationalEquivalenceProduct

variable (k : Type u) [Field k] [IsAlgClosed k] (V : Type u) [AddCommGroup V] [Module k V]
  [FiniteDimensional k V] [Nontrivial V]

omit [IsAlgClosed k] [FiniteDimensional k V] [Nontrivial V] in
/-- The family `C' ⊆ 𝐏(V) × ℙ¹`, contained in neither section when it dominates `ℙ¹`. -/
theorem not_range_subset_zeroSection_of_dense
    (Cfam : IrreducibleCloseds (projectiveLineProduct (projectiveSpaceOfModuleToSpec k V)))
    (hdom : closure ((pullback.snd (projectiveSpaceOfModuleToSpec k V)
      (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k))).base ''
        (Cfam : Set (projectiveLineProduct (projectiveSpaceOfModuleToSpec k V)))) = Set.univ) :
    ¬ Set.range (integralComponentAt Cfam.isIrreducible.genericPoint).subschemeι.base ⊆
        Set.range (zeroSection (projectiveSpaceOfModuleToSpec k V)).base ∧
      ¬ Set.range (integralComponentAt Cfam.isIrreducible.genericPoint).subschemeι.base ⊆
        Set.range (infinitySection (projectiveSpaceOfModuleToSpec k V)).base := by
  have hrange : Set.range (integralComponentAt Cfam.isIrreducible.genericPoint).subschemeι.base =
      (Cfam : Set (projectiveLineProduct (projectiveSpaceOfModuleToSpec k V))) := by
    rw [Scheme.IdealSheafData.range_subschemeι, coe_support_integralComponentAt,
      Cfam.isIrreducible.closure_genericPoint Cfam.isClosed']
  rw [hrange]
  -- the line has a point other than any given one
  have htwo : zeroLinePoint k ≠ infinityLinePoint k := by
    intro h
    exact Set.disjoint_iff.mp (disjoint_range_lineZeroSection_lineInfinitySection (Spec (.of k)))
      ⟨⟨_, rfl⟩, ⟨IsLocalRing.closedPoint k, h.symm⟩⟩
  -- a dominant family inside a closed point of the line fills out the line
  have key : ∀ p, IsClosed {p} → (Cfam : Set (projectiveLineProduct
      (projectiveSpaceOfModuleToSpec k V))) ⊆ (pullback.snd (projectiveSpaceOfModuleToSpec k V)
        (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k))).base ⁻¹' {p} →
      ∀ q, q = p := fun p hp hall q => by
    have := closure_mono (Set.image_subset_iff.2 hall)
    rw [hdom, hp.closure_eq] at this
    exact this (Set.mem_univ q)
  refine ⟨fun h => htwo.symm (key _ (isClosed_zeroLinePoint k) (fun y hy => ?_) _),
    fun h => htwo (key _ (isClosed_infinityLinePoint k) (fun y hy => ?_) _)⟩
  · obtain ⟨x, rfl⟩ := h hy
    exact snd_zeroSection_apply k _ x
  · obtain ⟨x, rfl⟩ := h hy
    exact snd_infinitySection_apply k _ x

/-- The reduced closed subscheme on an irreducible closed subset is the integral closed
subscheme attached to its generic point. -/
theorem vanishingIdeal_eq_integralComponentAt {T : Scheme.{u}} (A : IrreducibleCloseds T) :
    Scheme.IdealSheafData.vanishingIdeal (⟨A, A.isClosed'⟩ : Closeds T) =
      integralComponentAt A.isIrreducible.genericPoint := by
  rw [integralComponentAt]
  congr 1
  ext1
  exact (A.isIrreducible.closure_genericPoint A.isClosed').symm

/-- **The family moving the cone, with its dimensions.** Let `C ⊆ 𝐏(V)` be a closed subvariety
and `X ⊆ 𝐏(V)` a locally closed subvariety meeting it properly, with finitely many closed
subvarieties `T i ⊆ X` of dimension `r`. Then there is a closed subvariety `C' ⊆ 𝐏(V) × ℙ¹` with

* `C' → ℙ¹` dominant and `C'_0 = C` scheme theoretically;
* `C'` and `X × ℙ¹` intersecting properly;
* `dim C' = dim C + 1`;
* `dim (C'_∞ ∩ T i) + dim 𝐏(V) ≤ dim C + r` for every `i`. -/
theorem exists_family_data (N : ℕ) (hV : Module.finrank k V = N + 1)
    (C : IrreducibleCloseds (projectiveSpaceOfModule k V))
    (X : Set (projectiveSpaceOfModule k V)) (hX : IsLocallyClosed X) (hXirr : IsIrreducible X)
    (hCX : topologicalKrullDim ↥((C : Set (projectiveSpaceOfModule k V)) ∩ X) +
        topologicalKrullDim (projectiveSpaceOfModule k V) ≤
      topologicalKrullDim ↥(C : Set (projectiveSpaceOfModule k V)) + topologicalKrullDim ↥X)
    {ι : Type*} [Finite ι] (T : ι → Set (projectiveSpaceOfModule k V))
    (hTX : ∀ i, T i ⊆ X) (hTc : ∀ i, IsClosed {x : X | x.1 ∈ T i})
    (hTirr : ∀ i, IsIrreducible (T i)) (r : ℕ)
    (hTd : ∀ i, topologicalKrullDim ↥(T i) = (r : WithBot ℕ∞)) :
    ∃ Cfam : IrreducibleCloseds
        (projectiveLineProduct (projectiveSpaceOfModuleToSpec k V)),
      closure ((pullback.snd (projectiveSpaceOfModuleToSpec k V)
          (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k))).base ''
          (Cfam : Set (projectiveLineProduct (projectiveSpaceOfModuleToSpec k V)))) = Set.univ ∧
      zeroFiber (projectiveSpaceOfModuleToSpec k V)
          (integralComponentAt Cfam.isIrreducible.genericPoint) =
        integralComponentAt C.isIrreducible.genericPoint ∧
      topologicalKrullDim
            ↥((Cfam : Set (projectiveLineProduct (projectiveSpaceOfModuleToSpec k V))) ∩
            (pullback.fst (projectiveSpaceOfModuleToSpec k V)
              (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k))).base ⁻¹' X) +
          topologicalKrullDim (projectiveLineProduct (projectiveSpaceOfModuleToSpec k V)) ≤
        topologicalKrullDim
            ↥(Cfam : Set (projectiveLineProduct (projectiveSpaceOfModuleToSpec k V))) +
          topologicalKrullDim ↥((pullback.fst (projectiveSpaceOfModuleToSpec k V)
              (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k))).base ⁻¹' X) ∧
      relativeDimension (fieldChowSituation k).dimensionFunction
          (pullback.fst (projectiveSpaceOfModuleToSpec k V)
            (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) ≫
              projectiveSpaceOfModuleToSpec k V) Cfam.isIrreducible.genericPoint =
        relativeDimension (fieldChowSituation k).dimensionFunction
          (projectiveSpaceOfModuleToSpec k V) C.isIrreducible.genericPoint + 1 ∧
      ∀ i, topologicalKrullDim
            ↥((infinitySection (projectiveSpaceOfModuleToSpec k V)).base ⁻¹'
              (Cfam : Set (projectiveLineProduct (projectiveSpaceOfModuleToSpec k V))) ∩ T i) +
          (N : WithBot ℕ∞) ≤
        (((relativeDimension (fieldChowSituation k).dimensionFunction
          (projectiveSpaceOfModuleToSpec k V) C.isIrreducible.genericPoint).toNat + r : ℕ) :
            WithBot ℕ∞) := by
  obtain ⟨Cfam, h1, h2, h3, h4⟩ :=
    ProjectiveLineBridge.exists_movingFamily_projectiveLineProduct k V C X hX hXirr hCX T hTX hTc
      hTirr
  set W := integralComponentAt Cfam.isIrreducible.genericPoint with hWdef
  have : IsIntegral W.subscheme := isIntegral_integralComponentAt _
  rw [vanishingIdeal_eq_integralComponentAt, vanishingIdeal_eq_integralComponentAt] at h2
  obtain ⟨h₀, hInf⟩ := not_range_subset_zeroSection_of_dense k V Cfam h1
  have hrdC := Stacks.Chow.BertiniChain.relativeDimension_nonneg_of_field k
    (projectiveSpaceOfModuleToSpec k V) C.isIrreducible.genericPoint
  set c := relativeDimension (fieldChowSituation k).dimensionFunction
    (projectiveSpaceOfModuleToSpec k V) C.isIrreducible.genericPoint with hcdef
  have hk : schemeDeltaDimension (fieldChowSituation k)
      ((zeroFiber (projectiveSpaceOfModuleToSpec k V) W).subschemeι ≫
        projectiveSpaceOfModuleToSpec k V) = (c : EInt) := by
    rw [h2]
    exact schemeDeltaDimension_integralComponentAt_of_relativeDimension_eq _ _ _ rfl
  have hDim := relativeDimension_genericPoints_eq_of_schemeDeltaDimension_zeroFiber_eq
    (fieldChowSituation k) (projectiveSpaceOfModuleToSpec k V) W h₀ hk
  have hgenW : W.subschemeι.base (genericPoint W.subscheme) = Cfam.isIrreducible.genericPoint :=
    genericPointOf_integralComponentAt _
  have hrdfam : relativeDimension (fieldChowSituation k).dimensionFunction
      (pullback.fst (projectiveSpaceOfModuleToSpec k V)
        (relativeProjectiveLine (Spec (.of k)) ↘ Spec (.of k)) ≫
          projectiveSpaceOfModuleToSpec k V) Cfam.isIrreducible.genericPoint = c + 1 := by
    have h := hDim ⟨genericPoint W.subscheme, genericPoint_mem_genericPoints W.subscheme⟩
    rw [familyBase, relativeDimension_comp_closedImmersion, hgenW] at h
    exact h
  refine ⟨Cfam, h1, h2, h3, hrdfam, fun i => ?_⟩
  -- the infinity fibre has dimension at most `dim C`
  have hinfle := schemeDeltaDimension_infinityFiber_le (fieldChowSituation k)
    (projectiveSpaceOfModuleToSpec k V) W hDim hInf
  have hJ : JacobsonSpace (fieldChowSituation k).S :=
    inferInstanceAs (JacobsonSpace (Spec (CommRingCat.of k)))
  have hδ : ∀ q : (fieldChowSituation k).S, IsClosed ({q} : Set (fieldChowSituation k).S) →
      (fieldChowSituation k).dimensionFunction q = 0 := fun _ _ => rfl
  have hinfdim : topologicalKrullDim
      ↥((infinitySection (projectiveSpaceOfModuleToSpec k V)).base ⁻¹'
        (Cfam : Set (projectiveLineProduct (projectiveSpaceOfModuleToSpec k V)))) ≤
      ((c.toNat : ℕ) : WithBot ℕ∞) := by
    have hc' : (c : EInt) = ((c.toNat : ℕ) : ℤ) := by rw [Int.toNat_of_nonneg hrdC]
    rw [hc'] at hinfle
    have h := topologicalKrullDim_le_of_schemeDeltaDimension_le (fieldChowSituation k) hδ
      ((infinityFiber (projectiveSpaceOfModuleToSpec k V) W).subschemeι ≫
        projectiveSpaceOfModuleToSpec k V) c.toNat hinfle
    rw [← topologicalKrullDim_support_eq, coe_support_infinityFiber, hWdef,
      coe_support_integralComponentAt, Cfam.isIrreducible.closure_genericPoint Cfam.isClosed'] at h
    exact h
  have hP : topologicalKrullDim (projectiveSpaceOfModule k V) = (N : WithBot ℕ∞) :=
    topologicalKrullDim_projectiveSpaceOfModule_of_finrank_eq hV
  have h4i := h4 i
  rw [hP, hTd i] at h4i
  refine h4i.trans ?_
  rw [Nat.cast_add]
  exact add_le_add_left hinfdim _

end Stacks.Intersection.RationalEquivalenceProduct

end
