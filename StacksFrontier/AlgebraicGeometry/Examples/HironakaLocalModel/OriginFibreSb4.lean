module

public import StacksFrontier.AlgebraicGeometry.Examples.HironakaLocalModel.ExceptionalFamily
public import StacksFrontier.AlgebraicGeometry.Examples.HironakaLocalModel.SecondBlowupRing

/-!
# The fibres of the first blow-up of Hironaka's local model over its centre

Let `A = k[x, y, z]`, `I = (x, y)` and `b₁ : B₁ = Bl_I Spec A ⟶ Spec A` the first blow-up of the
local model of Hironaka's example. The centre `V(I) ≅ 𝔸¹_k` is smooth of relative dimension `1`
over `k` and `Spec A` is smooth of relative dimension `3`, so the conormal sheaf of `V(I)` is
locally free of rank two, and every fibre of `b₁` over a `k`-point of `V(I)` is the projective
line `𝐏¹_k` (`Stacks.AlgebraicGeometry.exists_iso_projectiveLine_of_isPullback_blowUpToBase`).

## Main results

* `Stacks.Examples.HironakaLocalModel.smoothOfRelativeDimension_centreIdeal_subschemeι_comp`:
  `V(x, y)` is smooth of relative dimension `1` over `k`.
* `Stacks.Examples.HironakaLocalModel.isFiniteLocallyFreeOfRank_two_conormal_centreIdeal`: the
  conormal sheaf of `V(x, y)` in `𝔸³_k` has rank two.
* `Stacks.Examples.HironakaLocalModel.exists_iso_projectiveLine_pullback_blowUpToBase_centreIdeal`:
  the fibre of `b₁` over a `k`-point `(0, 0, c)` of the centre is isomorphic over `k` to `𝐏¹_k`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits MvPolynomial
open Stacks.Examples.HironakaConicChart
open Stacks.AlgebraicGeometry.ProjPolyChart (polyGrading projToSpecCoeff)

universe u

attribute [local instance] MvPolynomial.gradedAlgebra

namespace Stacks.Examples.HironakaLocalModel

variable (k : Type u) [Field k]

/-- The parametrization `k[x, y, z]/(x, y) ≅ k[t]` of the centre, `z ↦ t`, as an isomorphism of
`k`-algebras. -/
def centreQuotientAlgEquiv :
    (Ring3 k ⧸ Ideal.span {X 0, (X 1 : Ring3 k)}) ≃ₐ[k] Polynomial k :=
  (Ideal.quotientEquivAlgOfEq k (ker_lineMap k).symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective (lineMap_surjective k))

/-- **The centre `V(x, y) ⊆ Spec k[x, y, z]` is smooth of relative dimension `1` over `k`.** -/
theorem smoothOfRelativeDimension_centreIdeal_subschemeι_comp :
    SmoothOfRelativeDimension 1 ((centreIdeal k).subschemeι ≫ ambientToBase k) := by
  set 𝔞 : Ideal (Ring3 k) := Ideal.span {X 0, (X 1 : Ring3 k)}
  have hI : idealSheafOf k 𝔞 = Scheme.IdealSheafData.ofIdealTop
      (Ideal.comap (Scheme.ΓSpecIso (CommRingCat.of (Ring3 k))).hom.hom 𝔞) := by
    rw [AlgebraicGeometry.Ideal.comap_hom_eq_map_inv]
  change SmoothOfRelativeDimension 1 ((idealSheafOf k 𝔞).subschemeι ≫ ambientToBase k)
  rw [hI]
  refine smoothOfRelativeDimension_of_isIso_comp 1 (Stacks.Blowup.specQuotientIsoSubscheme 𝔞).hom _
    ?_
  rw [Stacks.Blowup.specQuotientIsoSubscheme_hom_comp_subschemeι_assoc, ← Spec.map_comp,
    ← CommRingCat.ofHom_comp]
  rw [HasRingHomProperty.Spec_iff (P := @SmoothOfRelativeDimension 1)]
  refine RingHom.locally_of RingHom.isStandardSmoothOfRelativeDimension_respectsIso _ ?_
  change (algebraMap k (Ring3 k ⧸ 𝔞)).IsStandardSmoothOfRelativeDimension 1
  rw [RingHom.isStandardSmoothOfRelativeDimension_algebraMap]
  exact .of_algEquiv 1 ((MvPolynomial.uniqueAlgEquiv k (Fin 1)).trans
    (centreQuotientAlgEquiv k).symm)

/-- `Spec k[x, y, z]` is smooth over `k`. -/
instance smooth_ambientToBase : Smooth (ambientToBase k) :=
  haveI := smoothOfRelativeDimension_ambientToBase k
  SmoothOfRelativeDimension.smooth 3 _

/-- The centre `V(x, y)` is smooth over `k`. -/
instance smooth_centreIdeal_subschemeι_comp :
    Smooth ((centreIdeal k).subschemeι ≫ ambientToBase k) :=
  haveI := smoothOfRelativeDimension_centreIdeal_subschemeι_comp k
  SmoothOfRelativeDimension.smooth 1 _

/-- **The conormal sheaf of the centre `V(x, y)` in `𝔸³_k` is locally free of rank two**: the
relative dimensions over `k` are `3` and `1`. -/
instance isFiniteLocallyFreeOfRank_two_conormal_centreIdeal :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      (Stacks.Conormal.conormalSheafDegreeOne (centreIdeal k).subschemeι) 2 :=
  haveI : SmoothOfRelativeDimension (1 + 2) (ambientToBase k) :=
    smoothOfRelativeDimension_ambientToBase k
  haveI := smoothOfRelativeDimension_centreIdeal_subschemeι_comp k
  Stacks.AlgebraicGeometry.isFiniteLocallyFreeOfRank_two_conormalSheafDegreeOne
    (ambientToBase k) _ 1

/-- **The fibre of the first blow-up over a `k`-point of the centre is the projective line.** For
`c = (0, 0, c₂)`, the fibre `B₁ ×_{Spec A} Spec k` of `b₁ : Bl_{(x, y)} Spec k[x, y, z] ⟶
Spec k[x, y, z]` over the `k`-point `c` is isomorphic over `k` to `𝐏¹_k = Proj k[T₀, T₁]`. -/
theorem exists_iso_projectiveLine_pullback_blowUpToBase_centreIdeal (c : Fin 3 → k)
    (h0 : c 0 = 0) (h1 : c 1 = 0) :
    ∃ e : pullback (blowUpToBase (centreIdeal k)) (modelKPoint k c) ≅
        AlgebraicGeometry.Proj (polyGrading k 1),
      e.hom ≫ projToSpecCoeff k 1 = pullback.snd _ _ := by
  have hpt : modelKPoint k c (IsLocalRing.closedPoint k) = modelPoint k c :=
    modelKPoint_apply k c _
  have hmem : modelKPoint k c (IsLocalRing.closedPoint k) ∈ (centreIdeal k).support := by
    rw [hpt]
    refine (mem_support_idealSheafOf_iff k _ _).mpr (Ideal.span_le.mpr ?_)
    rintro _ (rfl | rfl) <;> exact (mem_modelPoint_iff k c _).mpr (by simp [h0, h1])
  obtain ⟨z, hz⟩ := exists_lift_subschemeι_of_mem_support (centreIdeal k) k (modelKPoint k c) _
    hmem
  have h : IsPullback (pullback.fst (blowUpToBase (centreIdeal k)) (modelKPoint k c))
      (pullback.snd _ _) (blowUpToBase (centreIdeal k)) (z ≫ (centreIdeal k).subschemeι) := by
    rw [hz]
    exact IsPullback.of_hasPullback _ _
  exact (Stacks.AlgebraicGeometry.exists_iso_projectiveLine_of_isPullback_blowUpToBase
    (ambientToBase k) (centreIdeal k) k z h).2

end Stacks.Examples.HironakaLocalModel

end
