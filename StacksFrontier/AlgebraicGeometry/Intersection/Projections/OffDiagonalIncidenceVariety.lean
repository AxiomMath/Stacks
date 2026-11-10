module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecialFibreDimension
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.CollinearityFibreScheme
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Product
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ClosedPointChain
public import StacksFrontier.AlgebraicGeometry.Variety.FibreDimensionTotal
public import StacksFrontier.AlgebraicGeometry.Variety.ImageDimension
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.RationalPointHyperplane

/-!
# The incidence variety of lines over the off-diagonal locus, and its dimension

Let `Y` and `Z` be closed subsets of `𝐏(V) = Proj (Sym_k V)` over a field `k`. This file
constructs the incidence variety

`T = {(y, z, p) : y ∈ Y ∖ Z, z ∈ Z, p on the line joining y and z}`

of the dimension count of [Stacks, Tag 0B1R], as
`AlgebraicGeometry.ProjectiveSpaceOfModule.incidenceVariety` over the open subscheme
`(Y ∖ Z) × Z` of the product of the closed subschemes attached to `Y` and `Z`, and shows that
`dim T ≤ dim Y + dim Z + 1` when `k` is algebraically closed.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpaceOfModule.offDiagLocus`: the open subset of `Y × Z` on which
  the first point avoids `Z`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.offDiagBase`: that open subset as a scheme, the base
  `(Y ∖ Z) × Z`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.offDiagIncidenceVariety`: the incidence variety of
  lines over `(Y ∖ Z) × Z`, with its projection
  `AlgebraicGeometry.ProjectiveSpaceOfModule.offDiagIncidenceVarietyToBase` to that base.

## Main results

* `AlgebraicGeometry.isRationalPoint_of_isClosed`: over an algebraically closed field a point
  closed in a scheme locally of finite type is a `k`-rational point.
* `AlgebraicGeometry.isClosed_singleton_image_of_locallyOfFiniteType`: the image of a closed point
  under a morphism of schemes locally of finite type over a field is a closed point.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_prodOfClosed`: the product of two
  closed subschemes of `𝐏(V)` has dimension `dim Y + dim Z`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.prodTwoFst_base_ne_prodTwoSnd_base`: the two points
  of a pair in the off-diagonal base are distinct.
* `topologicalKrullDimAt_fiber_offDiagIncidenceVarietyToBase_le_one`: the fibres of the
  off-diagonal incidence variety over its base are at most one-dimensional at the closed points.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_offDiagIncidenceVariety_le`: the
  off-diagonal incidence variety has dimension at most `dim Y + dim Z + 1`.

## References

* [Stacks Project, Tag 0B1R](https://stacks.math.columbia.edu/tag/0B1R)
-/
@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- Over an algebraically closed field a point closed in a scheme locally of finite type is a
rational point. -/
public theorem isRationalPoint_of_isClosed (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (x : X)
    (hx : IsClosed ({x} : Set X)) :
    IsRationalPoint f x := by
  set φ := Spec.preimage (X.fromSpecResidueField x ≫ f)
  have := isClosed_singleton_iff_isClosedImmersion.mp hx
  have hcomp : LocallyOfFiniteType (X.fromSpecResidueField x ≫ f) := inferInstance
  rw [← Spec.map_preimage (X.fromSpecResidueField x ≫ f),
    AlgebraicGeometry.HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hcomp
  let : Algebra k (X.residueField x) := φ.hom.toAlgebra
  let : Algebra.FiniteType k (X.residueField x) := by
    change RingHom.FiniteType (algebraMap k (X.residueField x))
    rw [RingHom.algebraMap_toAlgebra]
    exact hcomp
  let : Module.Finite k (X.residueField x) := finite_of_finite_type_of_isJacobsonRing _ _
  let : Algebra.IsIntegral k (X.residueField x) := Algebra.IsIntegral.of_finite _ _
  change IsIso φ
  rw [ConcreteCategory.isIso_iff_bijective]
  exact IsAlgClosed.algebraMap_bijective_of_isIntegral (k := k) (K := X.residueField x)

/-- The image of the `k`-point attached to a rational point is that point. -/
public theorem range_ptOfIsRationalPoint {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (x : X) (hx : IsRationalPoint f x) :
    Set.range (ptOfIsRationalPoint f x hx).base = {x} := by
  ext y
  simp only [Set.mem_range, Set.mem_singleton_iff]
  exact ⟨fun hw ↦ hw.choose_spec ▸ ptOfIsRationalPoint_apply f x hx hw.choose,
    fun h ↦ ⟨default, (ptOfIsRationalPoint_apply f x hx default).trans h.symm⟩⟩

/-- The image of a point closed in the source is closed in the target, for a morphism of schemes
locally of finite type over a field. -/
public theorem isClosed_singleton_image_of_locallyOfFiniteType (k : Type u) [Field k]
    {X Y : Scheme.{u}} (g : X ⟶ Y) (sX : X ⟶ Spec (.of k)) (sY : Y ⟶ Spec (.of k))
    [LocallyOfFiniteType sX] [LocallyOfFiniteType sY] (hg : g ≫ sY = sX) (x : X)
    (hx : IsClosed ({x} : Set X)) :
    IsClosed ({g.base x} : Set Y) := by
  refine isClosed_singleton_of_natTrdegResidueField_eq_zero k Y sY (g.base x) ?_
  have hzero := natTrdegResidueField_eq_zero_of_isClosed k X sX x hx
  let : Algebra k (Y.residueField (g.base x)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ sY.appTop ≫ Y.Γevaluation (g.base x)).hom.toAlgebra
  let : Algebra k (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ sX.appTop ≫ X.Γevaluation x).hom.toAlgebra
  let : FinTrdeg k (X.residueField x) := residueField_finTrdeg k sX x
  have hle := trdeg_residueField_map_le k g sX sY hg x
  have h1 : natTrdegResidueField k X sX x =
      Cardinal.toNat (Algebra.trdeg k (X.residueField x)) := rfl
  have h2 : natTrdegResidueField k Y sY (g.base x) =
      Cardinal.toNat (Algebra.trdeg k (Y.residueField (g.base x))) := rfl
  rw [h1] at hzero
  rw [h2]
  have := Cardinal.toNat_le_toNat hle (trdeg_lt_aleph0 k _)
  omega

namespace ProjectiveSpaceOfModule

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

/-! ### Closed subschemes of `𝐏(V)` and their products -/

/-- The inclusion of the closed subscheme attached to a closed subset of `𝐏(V)` is a closed
immersion. -/
public instance isClosedImmersion_closedSubschemeOfι (Y : Set (projectiveSpaceOfModule k V))
    (hY : IsClosed Y) : IsClosedImmersion (closedSubschemeOfι k V Y hY) :=
  inferInstanceAs
    (IsClosedImmersion (Scheme.IdealSheafData.vanishingIdeal ⟨Y, hY⟩).subschemeι)

/-- The points of the closed subscheme attached to a closed subset are that subset. -/
public theorem range_closedSubschemeOfι (Y : Set (projectiveSpaceOfModule k V))
    (hY : IsClosed Y) :
    Set.range (closedSubschemeOfι k V Y hY).base = Y :=
  ((Scheme.IdealSheafData.vanishingIdeal ⟨Y, hY⟩).range_subschemeι).trans
    (Scheme.IdealSheafData.coe_support_vanishingIdeal _)

/-- The closed subscheme attached to a closed subset has the dimension of that subset. -/
public theorem topologicalKrullDim_closedSubschemeOf (Y : Set (projectiveSpaceOfModule k V))
    (hY : IsClosed Y) :
    topologicalKrullDim (closedSubschemeOf k V Y hY) = topologicalKrullDim Y :=
  (Stacks.Chow.topologicalKrullDim_subscheme
      (Scheme.IdealSheafData.vanishingIdeal ⟨Y, hY⟩)).trans
    (congrArg (fun S : Set (projectiveSpaceOfModule k V) => topologicalKrullDim ↥S)
      (Scheme.IdealSheafData.coe_support_vanishingIdeal ⟨Y, hY⟩))

/-- The closed subscheme attached to a closed subset of `𝐏(V)` is locally of finite type over
`Spec k`. -/
public instance locallyOfFiniteType_closedSubschemeOfToSpec [FiniteDimensional k V]
    [Nontrivial V] (Y : Set (projectiveSpaceOfModule k V)) (hY : IsClosed Y) :
    LocallyOfFiniteType (closedSubschemeOfToSpec k V Y hY) := by
  have := isProper_projectiveSpaceOfModuleToSpec k V
  rw [closedSubschemeOfToSpec]
  infer_instance

variable [FiniteDimensional k V] [Nontrivial V] (Y Z : Set (projectiveSpaceOfModule k V))
    (hY : IsClosed Y) (hZ : IsClosed Z)

/-- The product of two closed subschemes of `𝐏(V)` is locally of finite type over
`𝐏(V) ×_k 𝐏(V)`. -/
public instance locallyOfFiniteType_prodOfClosedToProdTwo :
    LocallyOfFiniteType (prodOfClosedToProdTwo k V Y Z hY hZ) :=
  MorphismProperty.pullbackMap (P := @LocallyOfFiniteType)
    (inferInstance : LocallyOfFiniteType (closedSubschemeOfι k V Y hY))
    (inferInstance : LocallyOfFiniteType (closedSubschemeOfι k V Z hZ)) rfl rfl

/-- The structure morphism over `Spec k` of the product of two closed subschemes of `𝐏(V)`. -/
public def prodOfClosedToSpec : prodOfClosed k V Y Z hY hZ ⟶ Spec (.of k) :=
  prodOfClosedToProdTwo k V Y Z hY hZ ≫ prodTwoToSpec k V

/-- The product of two closed subschemes of `𝐏(V)` is locally of finite type over `Spec k`. -/
public instance locallyOfFiniteType_prodOfClosedToSpec :
    LocallyOfFiniteType (prodOfClosedToSpec k V Y Z hY hZ) := by
  rw [prodOfClosedToSpec]
  infer_instance

/-- The dimension of a product of two closed subschemes of `𝐏(V)` is the sum of the dimensions
of the two closed subsets. -/
public theorem topologicalKrullDim_prodOfClosed :
    topologicalKrullDim (prodOfClosed k V Y Z hY hZ) =
      topologicalKrullDim ↥Y + topologicalKrullDim ↥Z := by
  rw [show prodOfClosed k V Y Z hY hZ =
      pullback (closedSubschemeOfToSpec k V Y hY) (closedSubschemeOfToSpec k V Z hZ) from rfl,
    topologicalKrullDim_pullback k (closedSubschemeOfToSpec k V Y hY)
      (closedSubschemeOfToSpec k V Z hZ),
    topologicalKrullDim_closedSubschemeOf k V Y hY, topologicalKrullDim_closedSubschemeOf k V Z hZ]

/-- The first projection of the product of two closed subschemes of `𝐏(V)` to `𝐏(V)`. -/
public def prodOfClosedFst : prodOfClosed k V Y Z hY hZ ⟶ projectiveSpaceOfModule k V :=
  pullback.fst _ _ ≫ closedSubschemeOfι k V Y hY

/-- The second projection of the product of two closed subschemes of `𝐏(V)` to `𝐏(V)`. -/
public def prodOfClosedSnd : prodOfClosed k V Y Z hY hZ ⟶ projectiveSpaceOfModule k V :=
  pullback.snd _ _ ≫ closedSubschemeOfι k V Z hZ

omit [FiniteDimensional k V] [Nontrivial V] in
/-- The first projection of the product of closed subschemes computes the first projection of
`𝐏(V) ×_k 𝐏(V)`. -/
public theorem prodOfClosedToProdTwo_comp_prodTwoFst :
    prodOfClosedToProdTwo k V Y Z hY hZ ≫ prodTwoFst k V = prodOfClosedFst k V Y Z hY hZ :=
  pullback.lift_fst _ _ _

omit [FiniteDimensional k V] [Nontrivial V] in
/-- The second projection of the product of closed subschemes computes the second projection of
`𝐏(V) ×_k 𝐏(V)`. -/
public theorem prodOfClosedToProdTwo_comp_prodTwoSnd :
    prodOfClosedToProdTwo k V Y Z hY hZ ≫ prodTwoSnd k V = prodOfClosedSnd k V Y Z hY hZ :=
  pullback.lift_snd _ _ _

/-! ### The off-diagonal base `(Y ∖ Z) × Z` -/

/-- The off-diagonal locus of `Y × Z`: the open subset on which the first point avoids `Z`. -/
public def offDiagLocus : (prodOfClosed k V Y Z hY hZ).Opens :=
  prodOfClosedFst k V Y Z hY hZ ⁻¹ᵁ ⟨Zᶜ, hZ.isOpen_compl⟩

/-- The base `(Y ∖ Z) × Z` of the off-diagonal incidence variety, as an open subscheme of the
product of the two closed subschemes. -/
public abbrev offDiagBase : Scheme.{u} := (offDiagLocus k V Y Z hY hZ).toScheme

/-- The morphism of the off-diagonal base to `𝐏(V) ×_k 𝐏(V)`. -/
public def offDiagBaseToProdTwo : offDiagBase k V Y Z hY hZ ⟶ prodTwo k V :=
  (offDiagLocus k V Y Z hY hZ).ι ≫ prodOfClosedToProdTwo k V Y Z hY hZ

/-- The structure morphism of the off-diagonal base over `Spec k`. -/
public def offDiagBaseToSpec : offDiagBase k V Y Z hY hZ ⟶ Spec (.of k) :=
  offDiagBaseToProdTwo k V Y Z hY hZ ≫ prodTwoToSpec k V

/-- The off-diagonal base is locally of finite type over `𝐏(V) ×_k 𝐏(V)`. -/
public instance locallyOfFiniteType_offDiagBaseToProdTwo :
    LocallyOfFiniteType (offDiagBaseToProdTwo k V Y Z hY hZ) := by
  rw [offDiagBaseToProdTwo]
  infer_instance

/-- The off-diagonal base is locally of finite type over `Spec k`. -/
public instance locallyOfFiniteType_offDiagBaseToSpec :
    LocallyOfFiniteType (offDiagBaseToSpec k V Y Z hY hZ) := by
  rw [offDiagBaseToSpec]
  infer_instance

/-- The off-diagonal base has dimension at most `dim Y + dim Z`. -/
public theorem topologicalKrullDim_offDiagBase_le :
    topologicalKrullDim (offDiagBase k V Y Z hY hZ) ≤
      topologicalKrullDim ↥Y + topologicalKrullDim ↥Z := by
  rw [← topologicalKrullDim_prodOfClosed k V Y Z hY hZ]
  exact (offDiagLocus k V Y Z hY hZ).ι.isEmbedding.isInducing.topologicalKrullDim_le

/-- Projecting a point of the off-diagonal base to `𝐏(V)` can be computed in the product of the
two closed subschemes. -/
private theorem base_offDiagBaseToProdTwo_comp (k V : Type u) [Field k] [AddCommGroup V]
    [Module k V] (Y Z : Set (projectiveSpaceOfModule k V)) (hY : IsClosed Y) (hZ : IsClosed Z)
    {P : Scheme.{u}} (g : prodTwo k V ⟶ P)
    (h : prodOfClosed k V Y Z hY hZ ⟶ P) (hg : prodOfClosedToProdTwo k V Y Z hY hZ ≫ g = h)
    (b : offDiagBase k V Y Z hY hZ) :
    g.base ((offDiagBaseToProdTwo k V Y Z hY hZ).base b) =
      h.base ((offDiagLocus k V Y Z hY hZ).ι.base b) := by
  rw [offDiagBaseToProdTwo, Scheme.Hom.comp_apply, ← Scheme.Hom.comp_apply, hg]

omit [FiniteDimensional k V] [Nontrivial V] in
/-- The first point of a pair in the off-diagonal base avoids `Z`. -/
public theorem prodTwoFst_base_offDiagBaseToProdTwo_notMem (b : offDiagBase k V Y Z hY hZ) :
    (prodTwoFst k V).base ((offDiagBaseToProdTwo k V Y Z hY hZ).base b) ∉ Z := by
  rw [base_offDiagBaseToProdTwo_comp k V Y Z hY hZ _ _
    (prodOfClosedToProdTwo_comp_prodTwoFst k V Y Z hY hZ)]
  have hmem : (offDiagLocus k V Y Z hY hZ).ι.base b ∈ (offDiagLocus k V Y Z hY hZ : Set _) :=
    (Scheme.Opens.range_ι (offDiagLocus k V Y Z hY hZ)) ▸ Set.mem_range_self b
  exact hmem

omit [FiniteDimensional k V] [Nontrivial V] in
/-- The second point of a pair in the off-diagonal base lies in `Z`. -/
public theorem prodTwoSnd_base_offDiagBaseToProdTwo_mem (b : offDiagBase k V Y Z hY hZ) :
    (prodTwoSnd k V).base ((offDiagBaseToProdTwo k V Y Z hY hZ).base b) ∈ Z := by
  rw [base_offDiagBaseToProdTwo_comp k V Y Z hY hZ _ _
    (prodOfClosedToProdTwo_comp_prodTwoSnd k V Y Z hY hZ)]
  exact (range_closedSubschemeOfι k V Z hZ).subset (Set.mem_range_self _)

omit [FiniteDimensional k V] [Nontrivial V] in
/-- The two points of a pair in the off-diagonal base are distinct. -/
public theorem prodTwoFst_base_ne_prodTwoSnd_base (b : offDiagBase k V Y Z hY hZ) :
    (prodTwoFst k V).base ((offDiagBaseToProdTwo k V Y Z hY hZ).base b) ≠
      (prodTwoSnd k V).base ((offDiagBaseToProdTwo k V Y Z hY hZ).base b) := fun h ↦
  prodTwoFst_base_offDiagBaseToProdTwo_notMem k V Y Z hY hZ b
    (h ▸ prodTwoSnd_base_offDiagBaseToProdTwo_mem k V Y Z hY hZ b)

/-- The off-diagonal incidence variety: the triples `(y, z, p)` with `y` in `Y ∖ Z`, `z` in
`Z` and `p` on the line joining them. -/
public abbrev offDiagIncidenceVariety : Scheme.{u} :=
  incidenceVariety k V (offDiagBaseToProdTwo k V Y Z hY hZ)

/-! ### The dimension of the off-diagonal incidence variety -/

/-- The projection `collinearProj` of the collinearity subscheme is locally of finite type. -/
public instance locallyOfFiniteType_collinearProj :
    LocallyOfFiniteType (collinearProj k V) := by
  have := isProper_projectiveSpaceOfModuleToSpec k V
  have := isClosedImmersion_collinearSubschemeι k V
  rw [collinearProj, prFst]
  infer_instance

/-- The projection of the off-diagonal incidence variety to its base `(Y ∖ Z) × Z`. -/
public abbrev offDiagIncidenceVarietyToBase :
    offDiagIncidenceVariety k V Y Z hY hZ ⟶ offDiagBase k V Y Z hY hZ :=
  incidenceVarietyToBase k V (offDiagBaseToProdTwo k V Y Z hY hZ)

/-- The off-diagonal incidence variety is locally of finite type over its base. -/
public instance locallyOfFiniteType_offDiagIncidenceVarietyToBase :
    LocallyOfFiniteType (offDiagIncidenceVarietyToBase k V Y Z hY hZ) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (isPullback_incidenceVariety k V (offDiagBaseToProdTwo k V Y Z hY hZ)) inferInstance

/-- The structure morphism of the off-diagonal incidence variety over `Spec k`. -/
public def offDiagIncidenceVarietyToSpec :
    offDiagIncidenceVariety k V Y Z hY hZ ⟶ Spec (.of k) :=
  offDiagIncidenceVarietyToBase k V Y Z hY hZ ≫ offDiagBaseToSpec k V Y Z hY hZ

/-- The off-diagonal incidence variety is locally of finite type over `Spec k`. -/
public instance locallyOfFiniteType_offDiagIncidenceVarietyToSpec :
    LocallyOfFiniteType (offDiagIncidenceVarietyToSpec k V Y Z hY hZ) := by
  rw [offDiagIncidenceVarietyToSpec]
  infer_instance

/-- Over an algebraically closed field, the fibre of the off-diagonal incidence variety over its
base has dimension at most one at every closed point. -/
public theorem topologicalKrullDimAt_fiber_offDiagIncidenceVarietyToBase_le_one [IsAlgClosed k]
    (t : offDiagIncidenceVariety k V Y Z hY hZ)
    (ht : IsClosed ({t} : Set (offDiagIncidenceVariety k V Y Z hY hZ))) :
    topologicalKrullDimAt
        ((offDiagIncidenceVarietyToBase k V Y Z hY hZ).fiber
          ((offDiagIncidenceVarietyToBase k V Y Z hY hZ).base t))
        ((offDiagIncidenceVarietyToBase k V Y Z hY hZ).asFiber t) ≤ 1 := by
  have hb : IsClosed ({(offDiagIncidenceVarietyToBase k V Y Z hY hZ).base t} :
      Set (offDiagBase k V Y Z hY hZ)) :=
    isClosed_singleton_image_of_locallyOfFiniteType k
      (offDiagIncidenceVarietyToBase k V Y Z hY hZ)
      (offDiagIncidenceVarietyToSpec k V Y Z hY hZ) (offDiagBaseToSpec k V Y Z hY hZ) rfl t ht
  have hq : IsClosed ({(offDiagBaseToProdTwo k V Y Z hY hZ).base
                        ((offDiagIncidenceVarietyToBase k V Y Z hY hZ).base t)} :
      Set (prodTwo k V)) :=
    isClosed_singleton_image_of_locallyOfFiniteType k (offDiagBaseToProdTwo k V Y Z hY hZ)
      (offDiagBaseToSpec k V Y Z hY hZ) (prodTwoToSpec k V) rfl _ hb
  have hcl₁ := isClosed_singleton_image_of_locallyOfFiniteType k (prodTwoFst k V)
    (prodTwoToSpec k V) (projectiveSpaceOfModuleToSpec k V) rfl _ hq
  have hcl₂ := isClosed_singleton_image_of_locallyOfFiniteType k (prodTwoSnd k V)
    (prodTwoToSpec k V) (projectiveSpaceOfModuleToSpec k V) pullback.condition.symm _ hq
  have hrat := isRationalPoint_of_isClosed k (prodTwoToSpec k V) _ hq
  have hdim := topologicalKrullDim_fiber_collinearProj
    (ptOfIsRationalPoint (prodTwoToSpec k V) _ hrat)
    (ptOfIsRationalPoint_comp _ _ hrat)
    (range_ptOfIsRationalPoint (prodTwoToSpec k V) _ hrat) hcl₁ hcl₂
    (prodTwoFst_base_ne_prodTwoSnd_base k V Y Z hY hZ
      ((offDiagIncidenceVarietyToBase k V Y Z hY hZ).base t))
  have hw : (collinearProj k V).base
      ((incidenceVarietyToCollinear k V (offDiagBaseToProdTwo k V Y Z hY hZ)).base t) =
      (offDiagBaseToProdTwo k V Y Z hY hZ).base
        ((offDiagIncidenceVarietyToBase k V Y Z hY hZ).base t) :=
    congrArg
      (fun r : offDiagIncidenceVariety k V Y Z hY hZ ⟶ prodTwo k V => r.base t)
      (isPullback_incidenceVariety k V (offDiagBaseToProdTwo k V Y Z hY hZ)).w
  rw [topologicalKrullDimAt_fiber_eq_of_isPullback
    (isPullback_incidenceVariety k V (offDiagBaseToProdTwo k V Y Z hY hZ)) t]
  exact (topologicalKrullDimAt_le_topologicalKrullDim _).trans (hw ▸ hdim).le

/-- Over an algebraically closed field, the off-diagonal incidence variety has dimension at most
`dim Y + dim Z + 1`. -/
public theorem topologicalKrullDim_offDiagIncidenceVariety_le [IsAlgClosed k] :
    topologicalKrullDim (offDiagIncidenceVariety k V Y Z hY hZ) ≤
      topologicalKrullDim ↥Y + topologicalKrullDim ↥Z + 1 := by
  refine topologicalKrullDim_le_of_isClosed_singleton_fiber_add_target k
    (offDiagIncidenceVarietyToSpec k V Y Z hY hZ) (offDiagBaseToSpec k V Y Z hY hZ)
    (offDiagIncidenceVarietyToBase k V Y Z hY hZ) rfl fun t ht => ?_
  exact (add_le_add
    (topologicalKrullDimAt_fiber_offDiagIncidenceVarietyToBase_le_one k V Y Z hY hZ t ht)
    ((topologicalKrullDimAt_le_topologicalKrullDim _).trans
      (topologicalKrullDim_offDiagBase_le k V Y Z hY hZ))).trans (add_comm _ _).le

end ProjectiveSpaceOfModule

end AlgebraicGeometry

end
