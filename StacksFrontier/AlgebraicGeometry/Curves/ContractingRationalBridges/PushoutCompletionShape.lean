module

public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.UnionOfClosedSubschemes
public import StacksFrontier.AlgebraicGeometry.Curves.ContractingRationalBridges.PushoutCompletion
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.PowerSeries.BaseConstantCoeff
public import StacksCore.Tactic.StacksAttribute

/-!
# The completed local ring of the contraction of a rational bridge is a node

Let `k` be a field, let `X` be a proper scheme over `k` of dimension one with `H⁰(X, 𝒪_X) = k`
and at-worst-nodal singularities, and let `C ⊆ X` be a rational bridge (Tag 0E3M). Write `X'` for
the scheme-theoretic closure of `X \ C`, `k' = Γ(C, 𝒪_C)` and `k'' = Γ(C ∩ X', 𝒪)`, and let `Y`
be the pushout of `C ∩ X' ⟶ X'` along the collapse `C ∩ X' ⟶ Spec k'`. This file computes the
completed local ring of `Y` at the image `y` of `Spec k' ⟶ Y`: it is
```
{f ∈ k''⟦s⟧ : f(0) ∈ k'},
```
and when `C ∩ X'` consists of two points — equivalently when `k'' = k' × k'` — it is
`k'⟦s, t⟧/(st)`.

## Main results

* `Stacks.Curves.exists_ringEquiv_completedLocalRing_contraction_bridge` — the two shapes of
  the completed local ring, the clause of [Stacks, Tag 0E3M].

## Implementation notes

The cartesian square of [Stacks, Tag 0E36] presents `𝒪^∧_{Y, y}` as the fibre product of `k'`
and `∏_i 𝒪^∧_{X', x'_i}` over `∏_i k'_i`, where `k'' = ∏_i k'_i`
(`Stacks.Curves.exists_isPullback_completedLocalRing_pushout_bridge`). Each `x'_i` is a point of
`C ∩ X'`, where `X'` is smooth over `k`, so `𝒪_{X', x'_i}` is a one-dimensional regular local
ring and its completion is `k'_i⟦t⟧` by [Stacks, Tag 0C0S] in one variable
(`PowerSeries.exists_ringEquiv_powerSeries_of_isRegularLocalRing`), compatibly with the map to
`k'_i` of the square, which is surjective. Power series over a product being the product of the
power series rings (`PowerSeries.piRingEquiv`), the top of the square becomes the constant
coefficient of `k''⟦s⟧`, and the fibre product is then read off by
`PowerSeries.nonempty_ringEquiv_constantCoeffInBase_of_isPullback_data`.

In the split case the subring becomes the two-branch multicross ring
(`PowerSeries.nonempty_ringEquiv_multicross`), which is `k'⟦x, y⟧/(xy)` by
`Stacks.Curves.quotientAlgEquivMulticross`.

## References

* [Stacks Project, Tag 0E3M](https://stacks.math.columbia.edu/tag/0E3M)
* [Stacks Project, Tag 0E36](https://stacks.math.columbia.edu/tag/0E36)
* [Stacks Project, Tag 0C0S](https://stacks.math.columbia.edu/tag/0C0S)
* [Stacks Project, Tag 0C1U](https://stacks.math.columbia.edu/tag/0C1U)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Curves

/-- A family of rings each isomorphic to power series compatibly with maps `r i` has product
isomorphic to power series over the product, compatibly with the product of the `r i`. -/
theorem _root_.PowerSeries.exists_ringEquiv_pi {ι : Type*} {A : ι → Type*}
    [∀ i, CommRing (A i)] {K : ι → Type*} [∀ i, CommRing (K i)] (r : ∀ i, A i →+* K i)
    (h : ∀ i, ∃ e : A i ≃+* PowerSeries (K i), ∀ a, PowerSeries.constantCoeff (e a) = r i a) :
    ∃ Θ : (∀ i, A i) ≃+* PowerSeries (∀ i, K i),
      ∀ a, PowerSeries.constantCoeff (Θ a) =
        (RingHom.pi fun i => (r i).comp (Pi.evalRingHom A i)) a := by
  choose e he using h
  refine ⟨(RingEquiv.piCongrRight e).trans (PowerSeries.piRingEquiv K).symm,
    fun a => funext fun i => ?_⟩
  rw [← PowerSeries.constantCoeff_piRingEquiv K _ i, RingEquiv.trans_apply,
    RingEquiv.apply_symm_apply]
  exact he i (a i)

/-- If `K ≃ₐ[k] k × k`, the power series over `K` with constant coefficient in `k` form the ring
`k⟦x, y⟧/(xy)`. -/
theorem nonempty_ringEquiv_quotient_of_algEquiv_prod (k : Type u) [CommRing k] {K : Type*}
    [CommRing K] [Algebra k K] (e : K ≃ₐ[k] k × k) :
    Nonempty (↥(PowerSeries.constantCoeffInBase k K) ≃+*
      (MvPowerSeries (Fin 2) k ⧸
        Ideal.span {(MvPowerSeries.X 0 : MvPowerSeries (Fin 2) k) * MvPowerSeries.X 1})) := by
  obtain ⟨e₁⟩ := PowerSeries.nonempty_ringEquiv_constantCoeffInBase_congr
    (e.trans (AlgEquiv.piFinTwo k fun _ : Fin 2 => k).symm)
  obtain ⟨e₂⟩ := PowerSeries.nonempty_ringEquiv_multicross k 2
  exact ⟨e₁.trans (e₂.trans (quotientAlgEquivMulticross (k := k)).symm.toRingEquiv)⟩

/-- A point of the closure of the complement of a rational bridge coming from the intersection
lies over the bridge. -/
theorem complementaryCurveι_base_inclusion_mem_support {X : Scheme.{u}} {C : X.IdealSheafData}
    (w : intersectionWithComplementaryCurve C) :
    (complementaryCurveι C).base ((Scheme.IdealSheafData.inclusion
        (le_sup_right : complementaryCurveIdeal C ≤
          intersectionWithComplementaryCurveIdeal C)).base w) ∈ (C.support : Set X) := by
  rw [Stacks.Chow.inclusion_subschemeι_base]
  refine (mem_support_and_mem_support_complementaryCurveIdeal_of_mem_intersection ?_).1
  rw [← Scheme.IdealSheafData.range_subschemeι]
  exact ⟨w, rfl⟩

/-- The completed local ring of the closure of the complement of a rational bridge at a point
over the bridge is a power series ring over any residue field it surjects onto, compatibly with
the constant coefficient. -/
theorem exists_ringEquiv_powerSeries_completedLocalRing_complementaryCurve_bridge
    {k : Type u} [Field k] {X : Scheme.{u}} [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))]
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hdim : topologicalKrullDim X = 1) (hnodal : HasAtWorstNodalSingularities k X)
    {C : X.IdealSheafData} (hC : IsRationalBridge k X C) (x : complementaryCurve C)
    (hx : (complementaryCurveι C).base x ∈ (C.support : Set X)) {K : Type u} [Field K]
    (r : Scheme.completedLocalRing (complementaryCurve C) x →+* K)
    (hr : Function.Surjective r) :
    ∃ e : Scheme.completedLocalRing (complementaryCurve C) x ≃+* PowerSeries K,
      ∀ a, PowerSeries.constantCoeff (e a) = r a := by
  have : IsLocallyNoetherian (complementaryCurve C) :=
    LocallyOfFiniteType.isLocallyNoetherian (complementaryCurveι C ≫ (X ↘ Spec (.of k)))
  have : IsLocalRing (Scheme.completedLocalRing (complementaryCurve C) x) :=
    Scheme.completedLocalRing_isLocal _ _
  have : IsNoetherianRing (Scheme.completedLocalRing (complementaryCurve C) x) :=
    Scheme.completedLocalRing_isNoetherian _ _
  have : IsAdicComplete (IsLocalRing.maximalIdeal
        (Scheme.completedLocalRing (complementaryCurve C) x))
      (Scheme.completedLocalRing (complementaryCurve C) x) :=
    Scheme.completedLocalRing_isAdicComplete _ _
  let : Algebra k (Scheme.completedLocalRing (complementaryCurve C) x) :=
    Scheme.completedLocalRingAlgebra (complementaryCurveι C ≫ (X ↘ Spec (.of k))) x
  have : IsRegularLocalRing (Scheme.completedLocalRing (complementaryCurve C) x) :=
    isRegularLocalRing_iff_adicCompletion_maximalIdeal.mp
      (isRegularLocalRing_stalk_complementaryCurve_bridge hdim hnodal hC x hx)
  have hd : ringKrullDim (Scheme.completedLocalRing (complementaryCurve C) x) = 1 := by
    rw [← ringKrullDim_adicCompletion_maximalIdeal]
    exact ringKrullDim_stalk_complementaryCurve_bridge_eq_one hdim hnodal hC x hx
  exact PowerSeries.exists_ringEquiv_powerSeries_of_isRegularLocalRing k _ K hd r hr

/-- **The completed local ring of the contraction of a rational bridge at the image of
`Spec k'`.**  Let `k` be a field, `X` a proper scheme over `k` of dimension one with
`H⁰(X, 𝒪_X) = k` and at-worst-nodal singularities, and `C ⊆ X` a rational bridge; let `X'` be the
scheme-theoretic closure of `X \ C`, `k' = Γ(C, 𝒪_C)`, `k'' = Γ(C ∩ X', 𝒪)` and `Y` the pushout
of `C ∩ X' ⟶ X'` along `C ∩ X' ⟶ Spec k'`.  Let `y ∈ Y` be the image of `Spec k'`, the image of
every point of that spectrum.  Then
```
𝒪^∧_{Y, y} ≅ {f ∈ k''⟦s⟧ : f(0) ∈ k'},
```
and `𝒪^∧_{Y, y} ≅ k'⟦s, t⟧/(st)` when `C ∩ X'` has two points, that is when `k'' = k' × k'`. -/
@[stacks 0E3M "𝒪^∧_{Y,y} ≅ {f ∈ k''[[s]] : f(0) ∈ k'}, and ≅ k'[[s,t]]/(st) when k'' = k' × k'"]
theorem exists_ringEquiv_completedLocalRing_contraction_bridge
    (k : Type u) [Field k] (X : Scheme.{u}) [X.Over (Spec (.of k))]
    [IsProper (X ↘ Spec (.of k))]
    (hdim : topologicalKrullDim X = 1)
    [IsIso ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop)]
    (hnodal : HasAtWorstNodalSingularities k X)
    (C : X.IdealSheafData) (hC : IsRationalBridge k X C) :
    letI : IsIntegral C.subscheme := hC.isIntegral
    letI : Field Γ(C.subscheme, ⊤) :=
      (isField_of_universallyClosed k (C.subschemeι ≫ (X ↘ Spec (.of k)))).toField
    letI : Algebra Γ(C.subscheme, ⊤) Γ(intersectionWithComplementaryCurve C, ⊤) :=
      (Scheme.IdealSheafData.inclusion
        (le_sup_left : C ≤ intersectionWithComplementaryCurveIdeal C)).appTop.hom.toAlgebra
    ∃ y : pushoutScheme (bridgePushoutSituation hdim hnodal hC),
      (∀ p : (bridgePushoutSituation hdim hnodal hC).Y,
          pushoutInr (bridgePushoutSituation hdim hnodal hC) p = y) ∧
        Nonempty (Scheme.completedLocalRing
            (pushoutScheme (bridgePushoutSituation hdim hnodal hC)) y ≃+*
          ↥(PowerSeries.constantCoeffInBase (Γ(C.subscheme, ⊤) : Type u)
            (Γ(intersectionWithComplementaryCurve C, ⊤) : Type u))) ∧
        (Nonempty (Γ(intersectionWithComplementaryCurve C, ⊤) ≃ₐ[(Γ(C.subscheme, ⊤) : Type u)]
            ((Γ(C.subscheme, ⊤) : Type u) × (Γ(C.subscheme, ⊤) : Type u))) →
          Nonempty (Scheme.completedLocalRing
              (pushoutScheme (bridgePushoutSituation hdim hnodal hC)) y ≃+*
            (MvPowerSeries (Fin 2) (Γ(C.subscheme, ⊤) : Type u) ⧸
              Ideal.span {(MvPowerSeries.X 0 :
                              MvPowerSeries (Fin 2) (Γ(C.subscheme, ⊤) : Type u)) *
                            MvPowerSeries.X 1}))) := by
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
  obtain ⟨n, Ki, hKifield, hKialg, hKifin, x', y, bottomResidueMap, completionMap,
    componentResidueMap, ⟨eAlg⟩, hy, hx'w, hsurj, hpb⟩ :=
    exists_isPullback_completedLocalRing_pushout_bridge hdim hnodal hC
  let := hKifield
  let := hKialg
  have := hKifin
  have : Nontrivial (Γ(intersectionWithComplementaryCurve C, ⊤) : Type u) :=
    Module.nontrivial_of_finrank_pos (R := (Γ(C.subscheme, ⊤) : Type u))
      (by rw [hC.intersection_finrank_eq_two]; exact two_pos)
  have : Nontrivial (∀ i, Ki i) := eAlg.toEquiv.symm.nontrivial
  obtain ⟨Θ, hΘ⟩ := PowerSeries.exists_ringEquiv_pi componentResidueMap fun i => by
    obtain ⟨w, hw⟩ := hx'w i
    exact exists_ringEquiv_powerSeries_completedLocalRing_complementaryCurve_bridge hdim hnodal hC
      (x' i) (by rw [hw]; exact complementaryCurveι_base_inclusion_mem_support w)
      (componentResidueMap i) (hsurj i)
  have hgen : Nonempty (Scheme.completedLocalRing
      (pushoutScheme (bridgePushoutSituation hdim hnodal hC)) y ≃+*
      ↥(PowerSeries.constantCoeffInBase (Γ(C.subscheme, ⊤) : Type u)
        (Γ(intersectionWithComplementaryCurve C, ⊤) : Type u))) := by
    have e1 : Scheme.completedLocalRing
        (pushoutScheme (bridgePushoutSituation hdim hnodal hC)) y ≃+*
        ↥(RingHom.pullback
          (RingHom.pi fun i => algebraMap (Γ(C.subscheme, ⊤) : Type u) (Ki i))
          (RingHom.pi fun i => (componentResidueMap i).comp (Pi.evalRingHom _ i))) :=
      (hpb.isLimit.conePointUniqueUpToIso
        (CommRingCat.pullbackConeIsLimit _ _)).commRingCatIsoToRingEquiv
    obtain ⟨e2⟩ := PowerSeries.nonempty_ringEquiv_constantCoeffInBase_of_isPullback_data
      (Γ(C.subscheme, ⊤) : Type u) (∀ i, Ki i)
      (∀ i, Scheme.completedLocalRing (complementaryCurve C) (x' i))
      (RingHom.pi fun i => (componentResidueMap i).comp (Pi.evalRingHom _ i)) Θ hΘ
    obtain ⟨e3⟩ := PowerSeries.nonempty_ringEquiv_constantCoeffInBase_congr eAlg.symm
    exact ⟨e1.trans (e2.trans e3)⟩
  refine ⟨y, hy, hgen, fun ⟨esplit⟩ => ?_⟩
  obtain ⟨egen⟩ := hgen
  obtain ⟨e⟩ := nonempty_ringEquiv_quotient_of_algEquiv_prod _ esplit
  exact ⟨egen.trans e⟩

end Stacks.Curves

end
