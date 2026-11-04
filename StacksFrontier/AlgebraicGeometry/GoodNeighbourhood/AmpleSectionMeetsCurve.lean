module

public import StacksFrontier.AlgebraicGeometry.GoodNeighbourhood.GoodSections
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.ZeroSchemeOpenNeighbourhood
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.AlgebraicClosureBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SmoothSupportSpecialization
public import StacksFrontier.AlgebraicGeometry.SectionRingProjMorphism.ToSpecZero
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.BertiniVanishingCut

/-!
# A section of an ample module vanishes somewhere on a curve

Let `X` be proper over a field `k`, `M` an ample invertible module and `s` a global section of
`M`. If a closed subscheme `T` of `X` is smooth of positive relative dimension at some point,
then `s` vanishes at some point of `T`.

## Main results

* `AlgebraicGeometry.GoodNeighbourhood.exists_mem_support_zeroScheme_of_subschemeSmoothAt`: a
  global section of an ample invertible module on a proper scheme over a field vanishes at some
  point of every closed subscheme which is smooth of positive relative dimension at a point.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.GoodNeighbourhood

attribute [local instance] Stacks.SectionsVanishingOnSubscheme.isInvertible_of_isInvertibleModule

/-- A global section of an ample invertible module on a proper scheme over a field vanishes at
some point of every closed subscheme which is smooth of positive relative dimension at a point. -/
theorem exists_mem_support_zeroScheme_of_subschemeSmoothAt (k : Type u) [Field k]
    {X : Scheme.{u}} (p : X ⟶ Spec (.of k)) [IsProper p] (M : X.Modules)
    [Stacks.Ample.IsInvertibleModule X M] (hM : Stacks.Ample.IsAmple X M) (s : Γ(M, ⊤))
    (T : X.IdealSheafData) (r : ℕ) {x : X} (hx : SubschemeSmoothAt p T (r + 1) x) :
    ∃ z ∈ T.support, z ∈ (zeroScheme X M s).support := by
  by_contra h
  push Not at h
  have haff := Stacks.AmpleNonvanishingUniversallyClosed.isAffineOpen_nonvanishingOpen_of_isAmple
    M hM (Stacks.SectionRingProjMorphism.ToSpecZero.universallyClosed_toSpecΓ p) s
  set ι := T.subschemeι
  have htop : ι ⁻¹ᵁ Stacks.NonvanishingOpen.nonvanishingOpen X M s = ⊤ := by
    refine top_le_iff.mp fun y _ =>
      Stacks.Algebraization.mem_nonvanishingOpen_of_notMem_support_zeroScheme M s (h _ ?_)
    show ι y ∈ (T.support : Set X)
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨y, rfl⟩
  have : IsAffine (⊤ : T.subscheme.Opens).toScheme :=
    (htop ▸ haff.preimage ι : IsAffineOpen (⊤ : T.subscheme.Opens))
  have : IsAffine T.subscheme := IsAffine.of_isIso T.subscheme.topIso.inv
  have : IsFinite (ι ≫ p) :=
    (IsFinite.iff_isProper_and_isAffineHom (f := ι ≫ p)).2 ⟨inferInstance, inferInstance⟩
  have : DiscreteTopology T.subscheme :=
    AlgebraicGeometry.discreteTopology_of_isFinite_over_field k (ι ≫ p)
  obtain ⟨y, -, U, hyU, hsm⟩ := hx
  have hdim := topologicalKrullDimAt_eq_of_smoothOfRelativeDimension_over_field (r + 1)
    (U.ι ≫ ι ≫ p) ⟨y, hyU⟩
  have : DiscreteTopology U.toScheme :=
    inferInstanceAs (DiscreteTopology (U : Set T.subscheme))
  have hle : topologicalKrullDimAt U.toScheme ⟨y, hyU⟩ ≤ 0 :=
    (topologicalKrullDimAt_le_topologicalKrullDim _).trans
      (topologicalKrullDim_zero_of_discreteTopology _)
  rw [hdim] at hle
  exact absurd hle (by norm_cast)

end AlgebraicGeometry.GoodNeighbourhood

end
