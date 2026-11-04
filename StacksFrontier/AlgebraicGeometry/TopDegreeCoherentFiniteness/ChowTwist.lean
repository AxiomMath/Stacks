module

public import StacksFrontier.AlgebraicGeometry.TopDegreeCoherentFiniteness.QuasiProjective
public import StacksFrontier.AlgebraicGeometry.TopDegreeCoherentFiniteness.Supported
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowStalk
public import StacksFrontier.AlgebraicGeometry.Segre.ChartSurjective
public import StacksFrontier.AlgebraicGeometry.ChowNoetherian.Refinements
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.PseudoMorphism
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ProjectiveCompletion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Closure.ImmersionImage
public import StacksFrontier.AlgebraicGeometry.ProperCoherenceWitness.ChowTwist

/-!
# The Chow twist of a scheme separated and of finite type over a field

Chow's lemma ([Stacks, Tag 0200]) gives, for `Z` separated and of finite type over a field `k`, a
proper `π : Y ⟶ Z`, an isomorphism over a dense open, with `Y` immersed in `ℙⁿ_k`. A power `M` of
the pulled-back hyperplane sheaf has no higher direct images along `π` ([Stacks, Tag 02O1]).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Ample Stacks.RelativeVeryAmple Stacks.AmpleProjectiveImmersion

universe u

namespace AlgebraicGeometry.TopDegree

attribute [local instance 10000] HasDerivedCategory.standard

variable (k : Type u) [Field k]

/-- **The Chow twist.** -/
theorem exists_chowTwist {Z : Scheme.{u}} (f : Z ⟶ Spec (.of k)) [LocallyOfFiniteType f]
    [QuasiCompact f] [IsSeparated f] :
    ∃ (Y : Scheme.{u}) (π : Y ⟶ Z) (U : Z.Opens) (M : Y.Modules) (n : ℕ)
      (j : Y ⟶ ProjectiveSpace n (Spec (.of k))),
      IsProper π ∧ Dense (U : Set Z) ∧ IsIso (π ∣_ U) ∧ IsImmersion j ∧
        π ≫ f = j ≫ (ProjectiveSpace n (Spec (.of k)) ↘ Spec (.of k)) ∧
        topologicalKrullDim Y ≤ topologicalKrullDim Z ∧
        IsInvertibleModule Y M ∧ M.IsCoherent ∧
        ((Scheme.Modules.pushforward π).obj M).IsCoherent ∧
        ∀ q : ℕ, 0 < q → IsZero (((Scheme.Modules.pushforward π).rightDerived q).obj M) := by
  obtain ⟨n, X', π₀, i₀, U, hπ₀, -, hi₀, hcomm₀, hU, hiso₀⟩ := hasDenseChowModification f
  have := hπ₀
  have := hi₀
  have := hiso₀
  obtain ⟨Y, π, j, hπ, -, hj, hcomm, -, hiso, hdense⟩ :=
    exists_isSchemeTheoreticallyDense_chowModification f π₀ i₀ U hcomm₀ hU hiso₀
  have := hπ
  have := hj
  have := hiso
  have hZln : IsLocallyNoetherian Z := LocallyOfFiniteType.isLocallyNoetherian f
  have : CompactSpace Z := QuasiCompact.compactSpace_of_compactSpace f
  have hZn : IsNoetherian Z := { }
  have hYln : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian π
  -- dimension
  have hdimY : topologicalKrullDim Y ≤ topologicalKrullDim Z := by
    have hd : Dense ((π ⁻¹ᵁ U : Y.Opens) : Set Y) := dense_of_isSchemeTheoreticallyDense _ hdense
    have : IsNoetherian Y :=
      { __ := hYln, toCompactSpace := (QuasiCompact.compactSpace_of_compactSpace π) }
    have h1 := Stacks.CurveProjectiveCompletion.topologicalKrullDim_le_of_dense_isOpenImmersion k
      (π ⁻¹ᵁ U).ι ((π ⁻¹ᵁ U).ι ≫ π ≫ f) (π ≫ f) rfl (by simpa using hd)
    refine h1.trans ?_
    have h2 : topologicalKrullDim (π ⁻¹ᵁ U : Scheme.{u}) = topologicalKrullDim (U : Scheme.{u}) :=
      IsHomeomorph.topologicalKrullDim_eq _ (π ∣_ U).homeomorph.isHomeomorph
    rw [h2]
    exact U.ι.isOpenEmbedding.isEmbedding.isInducing.topologicalKrullDim_le
  -- relative ampleness
  let L : Y.Modules := (Scheme.Modules.pullback j).obj
    (projectiveSpaceTwistingSheaf n (Spec (.of k)))
  have hLinv : IsInvertibleModule Y L :=
    Stacks.TwistInvertibleOverBase.isInvertibleModule_pullback_projectiveSpaceTwistingSheaf
      (S := Spec (.of k)) n j
  have hLample : Stacks.RelativeAmple.IsRelativelyAmple (π ≫ f) L :=
    Stacks.ProjectiveSpace.isRelativelyAmple_of_exists_hasImmersionTwistOver (π ≫ f) L
      inferInstance ⟨1, le_rfl, n, j, hj, hcomm.symm, ⟨tensorPowModuleOneIso Y _⟩⟩
  have hLπ : Stacks.RelativeAmple.IsRelativelyAmple π L :=
    Stacks.RelativeAmpleCompositionPermanence.isRelativelyAmple_of_comp π f L hLample
      inferInstance
  have hO : (unitModule Y).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.structureSheaf_isCoherent Y
  obtain ⟨n₀, hn₀⟩ := open Stacks.AlgebraicGeometry.AmpleTwistAcyclicity in
    exists_isZero_rightDerivedPlus_pushforward_tensorPowModule π (unitModule Y) L hLπ
  have hpow : AlgebraicGeometry.SheafOfModules.IsInvertible Y.presheaf Y.ringCatSheaf.2
      (tensorPowModule Y L (n₀ : ℤ)) := isInvertibleModule_tensorPowModule Y L (n₀ : ℤ)
  have hMcoh : (Stacks.RelativeVeryAmple.tensorModules Y (unitModule Y)
      (tensorPowModule Y L (n₀ : ℤ))).IsCoherent :=
    AlgebraicGeometry.SheafOfModules.isCoherent_tensorSheaf_of_isInvertible Y
      (unitModule Y) (tensorPowModule Y L (n₀ : ℤ))
  have hMinv : IsInvertibleModule Y (Stacks.RelativeVeryAmple.tensorModules Y (unitModule Y)
      (tensorPowModule Y L (n₀ : ℤ))) :=
    Stacks.AmplePullbackPart1.isInvertibleModule_tensorModules Y (unitModule Y)
      (tensorPowModule Y L (n₀ : ℤ))
  refine ⟨Y, π, U, Stacks.RelativeVeryAmple.tensorModules Y (unitModule Y)
    (tensorPowModule Y L (n₀ : ℤ)), n, j, hπ, hU, hiso, hj, hcomm, hdimY, hMinv, hMcoh, ?_, ?_⟩
  · have := hMcoh
    exact ProperCoherenceWitness.isCoherent_pushforward π _
  · intro m hm
    exact (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ m _).2 (hn₀ n₀ m le_rfl hm)

end AlgebraicGeometry.TopDegree

end
