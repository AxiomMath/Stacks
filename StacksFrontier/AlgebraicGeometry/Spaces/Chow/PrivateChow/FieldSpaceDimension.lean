module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ClosedSubspaceCycle
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.IntegralClosedSubspaceMaps
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.JacobsonDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrivateChow.FieldSpaceSituation
public import StacksFrontier.AlgebraicGeometry.Spaces.IntersectionNumberComponents
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.InverseImageDeltaDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.PrincipalDivisorRationalEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.StructureSheafCycle

/-!
# Dimensions and δ-dimensions over a field

Over the base `Spec k` of `AlgebraicGeometry.Space.fieldSpaceSituation`, whose dimension function
is zero, the δ-dimension of an integral closed subspace of an algebraic space proper over `k` is
its dimension (Stacks 0EDW, the base being Jacobson), and the δ-dimension of a closed subspace of
dimension `d` is at most `d`.

## Main results

* `AlgebraicGeometry.Space.dimension_integralClosedSubspace_eq_deltaDimension`: the dimension of
  an integral closed subspace is its δ-dimension.
* `AlgebraicGeometry.Space.deltaDimensionSubspace_le_of_dimension_eq`: the δ-dimension of a closed
  subspace of dimension `d` is at most `d`.
* `AlgebraicGeometry.Space.fieldSpaceSituation_deltaValue_id`: the dimension function of `Spec k`
  over itself vanishes.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))

/-- The base `Spec k` is Jacobson. -/
theorem fieldSpaceSituation_hasJacobson :
    HasEtaleLocalProperty B (Spec (.of k)) hk (yoneda.obj (baseObject k B hk))
      (fun T : Scheme.{u} => JacobsonSpace T) :=
  hasEtaleLocalProperty_of_representable B (Spec (.of k)) hk (yoneda.obj (baseObject k B hk))
    (P := fun T : Scheme.{u} => JacobsonSpace T) (baseObject k B hk) (Iso.refl _)
    (inferInstanceAs (JacobsonSpace (Spec (.of k))))

variable (X : AlgebraicSpaces B (Spec (.of k)) hk) {f : X.1 ⟶ yoneda.obj (baseObject k B hk)}
    (hf : IsProper B (Spec (.of k)) hk f)

include hf in
/-- **The dimension of an integral closed subspace is its δ-dimension**, over `Spec k` with the
zero dimension function (Stacks 0EDW, parts (1) and (2)). -/
theorem dimension_integralClosedSubspace_eq_deltaDimension
    (W : IntegralClosedSubspace B (Spec (.of k)) hk X.1) :
    0 ≤ deltaDimension (fieldSpaceSituation k B hk) f W ∧
      dimension B (Spec (.of k)) hk W.subspace.toFunctor W.isClosedSubspace.1 =
        (((deltaDimension (fieldSpaceSituation k B hk) f W).toNat : ℕ∞) : WithBot ℕ∞) := by
  have hX := isGood_fieldSpaceSituation_of_isProper k B hk X hf
  obtain ⟨h0, htop⟩ := topologicalKrullDim_points_eq_deltaDimension (fieldSpaceSituation k B hk) f
    hX (fieldSpaceSituation_hasJacobson k B hk) (fun _ _ => rfl) W
  refine ⟨h0, ?_⟩
  rw [← htop, topologicalKrullDim_points_eq_dimension_of_isDecentSpace]
  exact isDecentSpace_of_isClosedSubspace B (Spec (.of k)) hk
    ((fieldSpaceSituation k B hk).isDecentSpace_of_isGood f hX) W.isClosedSubspace

include hf in
/-- **The δ-dimension of a closed subspace of dimension `d` is at most `d`**, over `Spec k` with
the zero dimension function. -/
theorem deltaDimensionSubspace_le_of_dimension_eq (Z : ClosedSubspaces B (Spec (.of k)) hk X.1)
    {d : ℕ} (hd : dimension B (Spec (.of k)) hk Z.1.toFunctor Z.2.1 = d) :
    deltaDimensionSubspace (fieldSpaceSituation k B hk) f
      (isGood_fieldSpaceSituation_of_isProper k B hk X hf) Z.1 Z.2 ≤ ((d : ℤ) : EInt) := by
  have hX := isGood_fieldSpaceSituation_of_isProper k B hk X hf
  have hdec := (fieldSpaceSituation k B hk).isDecentSpace_of_isGood f hX
  refine (deltaDimensionClosed_le_coe_iff (fieldSpaceSituation k B hk) f hX _ _ d).2 fun t ht => ?_
  let C : IrreducibleCloseds (points B (Spec (.of k)) hk X.1) :=
    IrreducibleCloseds.closureSingleton t
  let W := integralClosedSubspaceOfPoints B (Spec (.of k)) hk X.2 hdec C
  have hW : subspacePointSet B (Spec (.of k)) hk X.1 W.subspace = closure {t} :=
    subspacePointSet_integralClosedSubspaceOfPoints B (Spec (.of k)) hk X.2 hdec C
  have hgen : IsGenericPoint t (subspacePointSet B (Spec (.of k)) hk X.1 W.subspace) :=
    hW ▸ isGenericPoint_closure
  have hδ : deltaDimension (fieldSpaceSituation k B hk) f W =
      (fieldSpaceSituation k B hk).deltaValue f t :=
    deltaDimension_eq_of_isGenericPoint (fieldSpaceSituation k B hk) f X.2 W t hgen
  obtain ⟨h0, hdimW⟩ := dimension_integralClosedSubspace_eq_deltaDimension k B hk X hf W
  have hT : IsClosed (Set.range (pointsMap B (Spec (.of k)) hk Z.1.toFunctor Z.1.ι)) :=
    isClosed_range_pointsMap_of_isClosedImmersion B (Spec (.of k)) hk X.2 Z.1.ι Z.2.2
  have hsub : closure {t} ⊆ Set.range (pointsMap B (Spec (.of k)) hk Z.1.toFunctor Z.1.ι) :=
    hT.closure_subset_iff.2 (Set.singleton_subset_iff.2 ht)
  have hle : dimension B (Spec (.of k)) hk W.subspace.toFunctor W.isClosedSubspace.1 ≤
      dimension B (Spec (.of k)) hk Z.1.toFunctor Z.2.1 := by
    rw [dimension_eq_topologicalKrullDim_range_of_isClosedImmersion B (Spec (.of k)) hk X.2 hdec
        W.isClosedSubspace.1 W.subspace.ι W.isClosedSubspace.2,
      dimension_eq_topologicalKrullDim_range_of_isClosedImmersion B (Spec (.of k)) hk X.2 hdec
        Z.2.1 Z.1.ι Z.2.2]
    refine (Topology.IsEmbedding.inclusion ?_).isInducing.topologicalKrullDim_le
    intro x hx
    have hx' : x ∈ subspacePointSet B (Spec (.of k)) hk X.1 W.subspace := hx
    rw [hW] at hx'
    exact hsub hx'
  rw [hdimW, hd] at hle
  have : (deltaDimension (fieldSpaceSituation k B hk) f W).toNat ≤ d := by exact_mod_cast hle
  change (fieldSpaceSituation k B hk).deltaValue f t ≤ d
  omega

/-- **The dimension function of `Spec k` over itself vanishes**: the δ-value of the identity of
`Spec k` is zero at its point. -/
theorem fieldSpaceSituation_deltaValue_id
    (y : points B (Spec (.of k)) hk (yoneda.obj (baseObject k B hk))) :
    (fieldSpaceSituation k B hk).deltaValue (𝟙 _) y = 0 := by
  set Z := fieldSpacePoint k B hk
  obtain ⟨h0, hdim⟩ := topologicalKrullDim_points_eq_deltaDimension (fieldSpaceSituation k B hk)
    (𝟙 _) (isGood_fieldSpaceSituation_id k B hk) (fieldSpaceSituation_hasJacobson k B hk)
    (fun _ _ => rfl) Z
  have : Subsingleton (points B (Spec (.of k)) hk Z.subspace.toFunctor) :=
    (pointsHomeomorphOfIso B (Spec (.of k)) hk
      (asIso (⊤ : Subfunctor (yoneda.obj (baseObject k B hk))).ι)).injective.subsingleton
  have : DiscreteTopology (points B (Spec (.of k)) hk Z.subspace.toFunctor) :=
    ⟨Subsingleton.elim _ _⟩
  have hle := topologicalKrullDim_zero_of_discreteTopology
    (points B (Spec (.of k)) hk Z.subspace.toFunctor)
  rw [hdim] at hle
  have h1 : (deltaDimension (fieldSpaceSituation k B hk) (𝟙 _) Z).toNat ≤ 0 := by
    exact_mod_cast hle
  have hδZ : deltaDimension (fieldSpaceSituation k B hk) (𝟙 _) Z = 0 := by omega
  rw [Subsingleton.elim y (Z.ambientGenericPoint B (Spec (.of k)) hk), ← hδZ]
  exact (deltaDimension_eq_of_isGenericPoint (fieldSpaceSituation k B hk) (𝟙 _)
    (isAlgebraicSpace_yoneda B (Spec (.of k)) hk (baseObject k B hk)) Z _
    (Z.isGenericPoint_ambientGenericPoint B (Spec (.of k)) hk
      (isAlgebraicSpace_yoneda B (Spec (.of k)) hk (baseObject k B hk)))).symm

end AlgebraicGeometry.Space

end
