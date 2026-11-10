module

public import Mathlib.AlgebraicGeometry.AlgClosed.Basic
public import StacksFrontier.AlgebraicGeometry.IncidenceDistinctPairs.Basic
public import StacksFrontier.AlgebraicGeometry.IncidenceDistinctPairs.FibreLine
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.ClosedPointBound
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.LinearSubspaceQuotientMap
public import StacksFrontier.Topology.Dimension.OpenGeneralizingMap

/-!
# The fibres of the incidence variety over the distinct pairs are at most one-dimensional

Let `V` be a finite-dimensional vector space over an algebraically closed field `k`. The
projection `collinearProj` of the collinearity subscheme of `𝐏(V) ×_k 𝐏(V) ×_k 𝐏(V)` to the
first two factors has, over a *closed* point `w` of `𝐏(V) ×_k 𝐏(V)` whose two points are
distinct, a fibre of dimension at most one: the fibre is the line joining them.

This is the fibre bound the dimension count of Tag 0B1R consumes. Over a non-closed point of the
base it is false — see the implementation notes of
`StacksFrontier.AlgebraicGeometry.IncidenceDistinctPairs.FibreLine` — but a bound on the fibres over
the closed points of the base is all that is needed, because
`AlgebraicGeometry.fiberDimensionAt_le_of_isClosed_singleton` upgrades it to the bound at every
point of the source, which is what a dimension count of the total space uses.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_collinearLocus_inter_le_one`:
  **the collinear triples over a closed point of `𝐏(V) ×_k 𝐏(V)` with distinct points form a set
  of dimension at most one.**
* `AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_fiber_collinearProj_le_one`:
  **the scheme-theoretic fibre of `collinearProj` over such a point has dimension at most one.**
* `AlgebraicGeometry.ProjectiveSpaceOfModule.relativeDimensionLE_incidenceVarietyToBase`: **the
  incidence variety of lines over the distinct pairs has relative dimension at most one over its
  base**, at every point of the source. This is the fibre bound in the form the dimension count
  of Tag 0B1R consumes.

## Implementation notes

Over an algebraically closed field a closed point `w` of a scheme locally of finite type is a
rational point (`AlgebraicGeometry.pointOfClosedPoint`), so it is the image of a morphism
`σ : Spec k ⟶ 𝐏(V) ×_k 𝐏(V)` which is a section of the structure morphism. The morphism
`x ↦ (w, x)` it induces, `fibreSection` below, then exhibits the fibre of `prFst` over `w` as a
copy of `𝐏(V)`: the square it forms with `σ` is cartesian, by pasting with the square defining
the triple product, so its range is the set-theoretic fibre `prFst ⁻¹' {w}`, and it is a section
of `pr₃`. **No base-change of projective space is needed**, because the residue field of `w` is
`k` itself: the fibre is `𝐏(V)` on the nose and not `𝐏(κ(w) ⊗_k V)`.

Being a section of `pr₃` is what makes `pr₃` injective on that fibre, and that is the only
property of the fibre the dimension bound uses: a continuous injection of a quasi-sober space
into a Kolmogorov space does not raise the Krull dimension
(`Topology.topologicalKrullDim_le_of_injOn_specializes`). So the collinear triples over `w` inject
into the line joining the two points of `w`, whose dimension is one
(`AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_linearSubspace_eq_one` at
`AlgebraicGeometry.ProjectiveSpaceOfModule.finrank_quotient_lineSubmodule`). The same injectivity
lemma is used once more, for the closed immersion of the collinearity subscheme, so that neither
an inducing-map nor an image-dimension argument has to be set up.

## References

* [Stacks Project, Tag 0B1R](https://stacks.math.columbia.edu/tag/0B1R)
* [Stacks Project, Tag 0B0E](https://stacks.math.columbia.edu/tag/0B0E)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]
  [IsAlgClosed k] [FiniteDimensional k V] [Nontrivial V]

/-! ### The fibre of the triple product over a closed point of the double product -/

/-- **The morphism `x ↦ (w, x)` attached to a closed point `w` of `𝐏(V) ×_k 𝐏(V)`.** Over an
algebraically closed field a closed point is rational, so it is the image of a section
`Spec k ⟶ 𝐏(V) ×_k 𝐏(V)` of the structure morphism, and this is the induced morphism to the
triple product. -/
public def fibreSection {w : prodTwo k V} (hw : IsClosed ({w} : Set (prodTwo k V))) :
    projectiveSpaceOfModule k V ⟶ prodThree k V :=
  pullback.lift
    (projectiveSpaceOfModuleToSpec k V ≫ pointOfClosedPoint (prodTwoToSpec k V) w hw)
    (𝟙 _)
    (by rw [Category.assoc, pointOfClosedPoint_comp, Category.comp_id, Category.id_comp])

/-- **`fibreSection` is a section of the third projection.** -/
@[reassoc]
public theorem fibreSection_comp_pr₃ {w : prodTwo k V}
    (hw : IsClosed ({w} : Set (prodTwo k V))) :
    fibreSection k V hw ≫ pr₃ k V = 𝟙 _ :=
  pullback.lift_snd _ _ _

/-- The composite of `fibreSection` with the projection to the first two factors is the constant
morphism at `w`. -/
@[reassoc]
public theorem fibreSection_comp_prFst {w : prodTwo k V}
    (hw : IsClosed ({w} : Set (prodTwo k V))) :
    fibreSection k V hw ≫ prFst k V =
      projectiveSpaceOfModuleToSpec k V ≫ pointOfClosedPoint (prodTwoToSpec k V) w hw :=
  pullback.lift_fst _ _ _

/-- **The square formed by `fibreSection` and the rational point `w` is cartesian**: the fibre of
the projection to the first two factors over a rational point of `𝐏(V) ×_k 𝐏(V)` is `𝐏(V)`. It is
the square defining the triple product, with the trivial square of the identity of `Spec k`
pasted on its right. -/
public theorem isPullback_fibreSection {w : prodTwo k V}
    (hw : IsClosed ({w} : Set (prodTwo k V))) :
    IsPullback (fibreSection k V hw) (projectiveSpaceOfModuleToSpec k V) (prFst k V)
      (pointOfClosedPoint (prodTwoToSpec k V) w hw) := by
  refine IsPullback.of_right (h₁₂ := pr₃ k V) ?_ (fibreSection_comp_prFst k V hw)
    (IsPullback.of_hasPullback (prodTwoToSpec k V)
      (projectiveSpaceOfModuleToSpec k V)).flip
  rw [fibreSection_comp_pr₃, pointOfClosedPoint_comp]
  exact IsPullback.of_id_fst

/-- Applying the underlying map of both sides of an equation `f ≫ g = h` of morphisms of schemes
to a point. -/
private theorem base_comp_apply_eq {X Y Z : Scheme} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z}
    (e : f ≫ g = h) (x : X) : g.base (f.base x) = h.base x := by
  rw [← e]
  rfl

/-- **The range of `fibreSection` is the set-theoretic fibre of `prFst` over `w`.** -/
public theorem range_fibreSection {w : prodTwo k V}
    (hw : IsClosed ({w} : Set (prodTwo k V))) :
    Set.range (fibreSection k V hw).base = (prFst k V).base ⁻¹' {w} := by
  have hpt : ∀ a : Spec (CommRingCat.of k),
      (pointOfClosedPoint (prodTwoToSpec k V) w hw).base a = w := fun a =>
    pointOfClosedPoint_apply (prodTwoToSpec k V) w hw a
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨q, rfl⟩
    exact (base_comp_apply_eq (fibreSection_comp_prFst k V hw) q).trans (hpt _)
  · intro t ht
    obtain ⟨cp⟩ : Nonempty (Spec (CommRingCat.of k)) := ⟨IsLocalRing.closedPoint k⟩
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := prFst k V) (g := pointOfClosedPoint (prodTwoToSpec k V) w hw) t cp
      (by rwa [hpt])
    exact ⟨((isPullback_fibreSection k V hw).isoPullback.inv).base z,
      (base_comp_apply_eq (isPullback_fibreSection k V hw).isoPullback_inv_fst z).trans hz⟩

/-- **The third projection is injective on the fibre of `prFst` over a closed point.** It has a
section there, `fibreSection`. -/
public theorem injOn_pr₃_fibre {w : prodTwo k V} (hw : IsClosed ({w} : Set (prodTwo k V))) :
    Set.InjOn (pr₃ k V).base ((prFst k V).base ⁻¹' {w}) := by
  have hsec : ∀ q : projectiveSpaceOfModule k V,
      (pr₃ k V).base ((fibreSection k V hw).base q) = q := by
    intro q
    simpa using base_comp_apply_eq (fibreSection_comp_pr₃ k V hw) q
  intro t₁ ht₁ t₂ ht₂ heq
  rw [← range_fibreSection k V hw] at ht₁ ht₂
  obtain ⟨q₁, rfl⟩ := ht₁
  obtain ⟨q₂, rfl⟩ := ht₂
  rw [hsec q₁, hsec q₂] at heq
  rw [heq]

/-! ### The dimension bound -/

omit [IsAlgClosed k] [Nontrivial V] in
/-- Two hyperplanes of `V`, one contained in the other, are equal. -/
private theorem eq_of_le_of_finrank_quotient_eq_one {P Q : Submodule k V}
    (hP : Module.finrank k (V ⧸ P) = 1) (hQ : Module.finrank k (V ⧸ Q) = 1) (hle : P ≤ Q) :
    P = Q := by
  have h1 := P.finrank_quotient_add_finrank
  have h2 := Q.finrank_quotient_add_finrank
  exact Submodule.eq_of_le_of_finrank_eq hle (by omega)

/-- A closed subset of a quasi-sober space which a continuous map sends injectively into a subset
`B` of a Kolmogorov space has dimension at most that of `B`. -/
private theorem topologicalKrullDim_le_of_isClosed_injOn {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [QuasiSober X] [T0Space Y] {A : Set X} {B : Set Y} {f : X → Y}
    (hA : IsClosed A) (hf : Continuous f) (hAB : ∀ x ∈ A, f x ∈ B) (hinj : A.InjOn f) :
    topologicalKrullDim A ≤ topologicalKrullDim B := by
  have : QuasiSober A := hA.isClosedEmbedding_subtypeVal.quasiSober
  exact Topology.topologicalKrullDim_le_of_injOn_specializes
    (fun a : A => (⟨f a, hAB a a.2⟩ : B)) ((hf.comp continuous_subtype_val).subtype_mk _)
    fun a b _ he => Subtype.ext (hinj a.2 b.2 (congrArg Subtype.val he))

/-- **The collinear triples over a closed point of `𝐏(V) ×_k 𝐏(V)` whose two points are distinct
form a set of dimension at most one.** The third point of such a triple lies on the line joining
the two points of the pair, and the third projection is injective on the fibre, so the set
injects continuously into that line, whose dimension is one. -/
public theorem topologicalKrullDim_collinearLocus_inter_le_one {w : prodTwo k V}
    (hw : IsClosed ({w} : Set (prodTwo k V)))
    (hne : (pullback.fst (projectiveSpaceOfModuleToSpec k V)
          (projectiveSpaceOfModuleToSpec k V)).base w ≠
        (pullback.snd (projectiveSpaceOfModuleToSpec k V)
          (projectiveSpaceOfModuleToSpec k V)).base w) :
    topologicalKrullDim
        ((collinearLocus k V ∩ (prFst k V).base ⁻¹' {w} : Set (prodThree k V))) ≤
      (1 : WithBot ℕ∞) := by
  set y := (pullback.fst (projectiveSpaceOfModuleToSpec k V)
    (projectiveSpaceOfModuleToSpec k V)).base w
  set z := (pullback.snd (projectiveSpaceOfModuleToSpec k V)
    (projectiveSpaceOfModuleToSpec k V)).base w
  have : JacobsonSpace (projectiveSpaceOfModule k V) :=
    LocallyOfFiniteType.jacobsonSpace (projectiveSpaceOfModuleToSpec k V)
  have hyc : IsClosed ({y} : Set (projectiveSpaceOfModule k V)) :=
    (pullback.fst (projectiveSpaceOfModuleToSpec k V)
      (projectiveSpaceOfModuleToSpec k V)).closedPoints_subset_preimage_closedPoints hw
  have hzc : IsClosed ({z} : Set (projectiveSpaceOfModule k V)) :=
    (pullback.snd (projectiveSpaceOfModuleToSpec k V)
      (projectiveSpaceOfModuleToSpec k V)).closedPoints_subset_preimage_closedPoints hw
  -- the two hyperplanes of degree-one equations are distinct, hence incomparable
  have hPQ : pointSubmodule k V y ≠ pointSubmodule k V z := fun h =>
    hne (eq_of_pointSubmodule_eq k V hyc hzc h)
  have hP1 := finrank_quotient_pointSubmodule k V y hyc
  have hQ1 := finrank_quotient_pointSubmodule k V z hzc
  have hnotle : ¬ pointSubmodule k V y ≤ pointSubmodule k V z := fun hle =>
    hPQ (eq_of_le_of_finrank_quotient_eq_one k V hP1 hQ1 hle)
  have hnotge : ¬ pointSubmodule k V z ≤ pointSubmodule k V y := fun hle =>
    hPQ (eq_of_le_of_finrank_quotient_eq_one k V hQ1 hP1 hle).symm
  -- the line joining the two points of the pair
  set L : Set (projectiveSpaceOfModule k V) := linearSubspace k V (lineSubmodule k V y z) with hL
  have hLdim : topologicalKrullDim L = 1 :=
    topologicalKrullDim_linearSubspace_eq_one k V _
      (finrank_quotient_lineSubmodule k V hyc hzc hne)
  set A : Set (prodThree k V) := collinearLocus k V ∩ (prFst k V).base ⁻¹' {w}
  -- the third point of a collinear triple over `w` lies on that line
  have hmem : ∀ t ∈ A, (pr₃ k V).base t ∈ L := by
    rintro t ⟨htc, htw⟩
    have h1 : (pr₁ k V).base t = y := by
      have h : (pr₁ k V).base t = (pullback.fst (projectiveSpaceOfModuleToSpec k V)
          (projectiveSpaceOfModuleToSpec k V)).base ((prFst k V).base t) := rfl
      rw [h, htw]
    have h2 : (pr₂ k V).base t = z := by
      have h : (pr₂ k V).base t = (pullback.snd (projectiveSpaceOfModuleToSpec k V)
          (projectiveSpaceOfModuleToSpec k V)).base ((prFst k V).base t) := rfl
      rw [h, htw]
    have ha : ∃ a ∈ pointSubmodule k V ((pr₁ k V).base t),
        a ∉ pointSubmodule k V ((pr₂ k V).base t) := by
      rw [h1, h2]
      exact IsConcreteLE.not_le_iff_exists.mp hnotle
    have hb : ∃ b ∈ pointSubmodule k V ((pr₂ k V).base t),
        b ∉ pointSubmodule k V ((pr₁ k V).base t) := by
      rw [h1, h2]
      exact IsConcreteLE.not_le_iff_exists.mp hnotge
    rw [hL, mem_linearSubspace_iff, lineSubmodule, ← h1, ← h2]
    exact pointSubmodule_inf_le_pointSubmodule_of_collinear k V htc ha hb
  -- `A` is closed, hence quasi-sober, and the third projection injects it into the line
  exact (topologicalKrullDim_le_of_isClosed_injOn
    ((isClosed_collinearLocus k V).inter (hw.preimage (Scheme.Hom.continuous (prFst k V))))
    (Scheme.Hom.continuous (pr₃ k V)) hmem
    ((injOn_pr₃_fibre k V hw).mono Set.inter_subset_right)).trans_eq hLdim

/-- **The fibre of the projection of the collinearity subscheme to the first two factors over a
closed point whose two points are distinct has dimension at most one.** This is the fibre bound
of Tag 0B1R: the fibre is the line joining the two points. -/
public theorem topologicalKrullDim_fiber_collinearProj_le_one {w : prodTwo k V}
    (hw : IsClosed ({w} : Set (prodTwo k V)))
    (hne : (pullback.fst (projectiveSpaceOfModuleToSpec k V)
          (projectiveSpaceOfModuleToSpec k V)).base w ≠
        (pullback.snd (projectiveSpaceOfModuleToSpec k V)
          (projectiveSpaceOfModuleToSpec k V)).base w) :
    topologicalKrullDim ((collinearProj k V).fiber w) ≤ (1 : WithBot ℕ∞) := by
  refine topologicalKrullDim_fiber_le_of_preimage_subset (collinearProj k V) w
    ((collinearProj k V).base ⁻¹' {w}) subset_rfl ?_
  have := isClosedImmersion_collinearSubschemeι k V
  have hemb : Topology.IsClosedEmbedding (collinearSubschemeι k V).base :=
    IsClosedImmersion.isClosedEmbedding (collinearSubschemeι k V)
  set Z : Set (collinearSubscheme k V) := (collinearProj k V).base ⁻¹' {w}
  set A : Set (prodThree k V) := collinearLocus k V ∩ (prFst k V).base ⁻¹' {w}
  have hmap : ∀ c ∈ Z, (collinearSubschemeι k V).base c ∈ A := by
    intro c hc
    refine ⟨(range_collinearSubschemeι k V).subset (Set.mem_range_self c), ?_⟩
    have h : (prFst k V).base ((collinearSubschemeι k V).base c) =
        (collinearProj k V).base c := rfl
    rw [Set.mem_preimage, h]
    exact hc
  exact le_trans (topologicalKrullDim_le_of_isClosed_injOn
    (hw.preimage (Scheme.Hom.continuous (collinearProj k V)))
    (Scheme.Hom.continuous (collinearSubschemeι k V)) hmap hemb.injective.injOn)
    (topologicalKrullDim_collinearLocus_inter_le_one k V hw hne)

/-! ### The relative dimension of the incidence variety over the distinct pairs -/

/-- The structure morphism `𝐏(V) ⟶ Spec k` is locally of finite type, being proper. -/
public instance locallyOfFiniteType_projectiveSpaceOfModuleToSpec' :
    LocallyOfFiniteType (projectiveSpaceOfModuleToSpec k V) := by
  have := isProper_projectiveSpaceOfModuleToSpec k V
  infer_instance

/-- The inclusion of the collinearity subscheme into `𝐏(V) ×_k 𝐏(V) ×_k 𝐏(V)` is a closed
immersion. -/
public instance isClosedImmersion_collinearSubschemeι' :
    IsClosedImmersion (collinearSubschemeι k V) :=
  isClosedImmersion_collinearSubschemeι k V

/-- The projection `prFst` of the triple product to its first two factors is locally of finite
type, as the base change of the structure morphism of `𝐏(V)`. -/
public instance locallyOfFiniteType_prFst : LocallyOfFiniteType (prFst k V) :=
  MorphismProperty.of_isPullback
    (IsPullback.of_hasPullback (prodTwoToSpec k V)
      (projectiveSpaceOfModuleToSpec k V)).flip inferInstance

/-- The incidence variety over `f : S ⟶ 𝐏(V) ×_k 𝐏(V)` is locally of finite type over `S`, as the
base change along `f` of the projection of the collinearity subscheme. -/
public instance locallyOfFiniteType_incidenceVarietyToBase {S : Scheme.{u}}
    (f : S ⟶ prodTwo k V) : LocallyOfFiniteType (incidenceVarietyToBase k V f) :=
  MorphismProperty.of_isPullback (IsPullback.of_hasPullback (collinearProj k V) f) inferInstance

/-- **The incidence variety of lines over the distinct pairs has relative dimension at most one
over its base.** Over a closed point of the base the two points of the pair are distinct closed
points of `𝐏(V)` and the fibre is the line joining them, of dimension one; the bound at every
point of the source follows by upper semicontinuity of the local fibre dimension.

This is the input the dimension count of Tag 0B1R consumes: together with
`AlgebraicGeometry.RelativeDimensionLE.comp` (Tag 02NL) and the dimension of the base
(`AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_prodOfClosedOffSnd_le`, which is
Tag 0B2M) it bounds the dimension of the incidence variety by `dim Y + dim Z + 1`. -/
public theorem relativeDimensionLE_incidenceVarietyToBase
    (Y Z : Set (projectiveSpaceOfModule k V)) (hY : IsClosed Y) (hZ : IsClosed Z) :
    RelativeDimensionLE
      (incidenceVarietyToBase k V (prodOfClosedOffSndToProdTwo k V Y Z hY hZ)) 1 := by
  have : LocallyOfFiniteType (closedSubschemeOfToSpec k V Y hY) :=
    inferInstanceAs (LocallyOfFiniteType
      ((Scheme.IdealSheafData.vanishingIdeal
          (⟨Y, hY⟩ : Closeds (projectiveSpaceOfModule k V))).subschemeι ≫
        projectiveSpaceOfModuleToSpec k V))
  have : LocallyOfFiniteType (closedSubschemeOfToSpec k V Z hZ) :=
    inferInstanceAs (LocallyOfFiniteType
      ((Scheme.IdealSheafData.vanishingIdeal
          (⟨Z, hZ⟩ : Closeds (projectiveSpaceOfModule k V))).subschemeι ≫
        projectiveSpaceOfModuleToSpec k V))
  set f := prodOfClosedOffSndToProdTwo k V Y Z hY hZ with hfdef
  -- the structure morphism of the base, and the finite-type and Jacobson instances it carries
  have hmapfst : prodOfClosedToProdTwo k V Y Z hY hZ ≫
      pullback.fst (projectiveSpaceOfModuleToSpec k V) (projectiveSpaceOfModuleToSpec k V) =
      pullback.fst (closedSubschemeOfToSpec k V Y hY) (closedSubschemeOfToSpec k V Z hZ) ≫
        closedSubschemeOfι k V Y hY := pullback.lift_fst _ _ _
  have hfstlft : LocallyOfFiniteType (pullback.fst (closedSubschemeOfToSpec k V Y hY)
      (closedSubschemeOfToSpec k V Z hZ)) :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback _ _).flip inferInstance
  have hcomp : prodOfClosedToProdTwo k V Y Z hY hZ ≫ prodTwoToSpec k V =
      pullback.fst (closedSubschemeOfToSpec k V Y hY) (closedSubschemeOfToSpec k V Z hZ) ≫
        closedSubschemeOfToSpec k V Y hY := by
    rw [prodTwoToSpec, ← Category.assoc, hmapfst]
    exact Category.assoc _ _ _
  have : LocallyOfFiniteType (prodOfClosedToProdTwo k V Y Z hY hZ ≫ prodTwoToSpec k V) := by
    rw [hcomp]
    exact MorphismProperty.comp_mem _ _ _ hfstlft inferInstance
  have : LocallyOfFiniteType (prodOfClosedToProdTwo k V Y Z hY hZ) :=
    locallyOfFiniteType_of_comp _ (prodTwoToSpec k V)
  have : LocallyOfFiniteType f := by
    rw [hfdef, prodOfClosedOffSndToProdTwo]
    exact MorphismProperty.comp_mem _ _ _ inferInstance inferInstance
  have : JacobsonSpace (prodTwo k V) :=
    LocallyOfFiniteType.jacobsonSpace (prodTwoToSpec k V)
  have : JacobsonSpace (incidenceVariety k V f) :=
    LocallyOfFiniteType.jacobsonSpace
      (incidenceVarietyToBase k V f ≫ f ≫ prodTwoToSpec k V)
  intro x
  refine fiberDimensionAt_le_of_isClosed_singleton (incidenceVarietyToBase k V f)
    (fun t ht => ?_) x
  -- the point of the collinearity subscheme below `t`, and the closed point of `𝐏(V) ×_k 𝐏(V)`
  have hsq := isPullback_incidenceVariety k V f
  have hbase : (collinearProj k V).base ((incidenceVarietyToCollinear k V f).base t) =
      f.base ((incidenceVarietyToBase k V f).base t) :=
    base_comp_apply_eq hsq.w t
  have hwclosed : IsClosed ({f.base ((incidenceVarietyToBase k V f).base t)} :
      Set (prodTwo k V)) := by
    have h : (incidenceVarietyToBase k V f ≫ f).base t ∈ closedPoints (prodTwo k V) :=
      (incidenceVarietyToBase k V f ≫ f).closedPoints_subset_preimage_closedPoints ht
    rw [Scheme.Hom.comp_apply] at h
    exact h
  have hwne := fst_ne_snd_prodOfClosedOffSndToProdTwo k V Y Z hY hZ
    ((incidenceVarietyToBase k V f).base t)
  rw [topologicalKrullDimAt_fiber_eq_of_isPullback hsq t]
  refine le_trans (topologicalKrullDimAt_le_topologicalKrullDim _) ?_
  rw [hbase]
  exact topologicalKrullDim_fiber_collinearProj_le_one k V hwclosed hwne

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
