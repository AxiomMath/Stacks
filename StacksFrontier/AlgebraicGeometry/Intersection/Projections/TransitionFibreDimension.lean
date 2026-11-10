module

public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.TransitionBase
public import StacksFrontier.AlgebraicGeometry.Intersection.Projections.TransitionLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.BaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.ClosedPointBound
public import StacksFrontier.AlgebraicGeometry.Variety.FibreDimension
public import StacksFrontier.Topology.Dimension.LocalKrullDim
public import StacksFrontier.Topology.Dimension.OpenGeneralizingMap

/-!
# The incidence correspondence of Tag 0B1S has dimension at most `dim X + dim Y + (dim V)² - dim V`

The fibre of the projection `T ⟶ 𝐏(V) ×_k 𝐏(V)` of the incidence correspondence of Tag 0B1S over
a pair of closed points `([f], [f'])` is the projective linear subspace of the parameter space cut
out by `AlgebraicGeometry.ProjectiveSpaceOfModule.transitionEquations`, of dimension
`(dim V)² - dim V` by
`AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_linearSubspace_transitionEquations`.
This file turns that computation into a bound on the dimension of the correspondence over the
product of two closed subvarieties.

The identification of the fibre is available only at *triples* of closed points, because
`AlgebraicGeometry.ProjectiveSpaceOfModule.mem_transitionLocus_iff_of_linearFunctionalPoint`
evaluates the minor sections of `𝒪(1,1,1)` against three linear functionals. That is enough:
the fibre is closed in the Jacobson space `𝐏(V) ×_k 𝐏(V) ×_k 𝐏`, so a containment of closed sets
checked at the closed points holds everywhere, by
`Set.subset_of_isClosed_of_closedPoints_subset`.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpaceOfModule.transitionFibreSection`: the section
  `[g] ↦ (w, [g])` of the projection to the parameter space over a closed point `w` of
  `𝐏(V) ×_k 𝐏(V)`, exhibiting the fibre of `tpFst` over `w` as a copy of `𝐏`.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_transitionLocus_inter_le`: the
  transition locus over a closed point of `𝐏(V) ×_k 𝐏(V)` has dimension at most `(dim V)² - dim V`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_fiber_transitionProj_le`: so does
  the fibre of the projection of the correspondence to `𝐏(V) ×_k 𝐏(V)` over such a point.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.relativeDimensionLE_transitionVarietyToBase`: the
  projection of the correspondence over the product of two closed subvarieties to that base has
  relative dimension at most `(dim V)² - dim V`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_transitionVariety_le`: **the
  correspondence over `X × Y` has dimension at most `dim X + dim Y + (dim V)² - dim V`.**

## Implementation notes

**Where this sits in Tag 0B1S.** The clause-(2) half of the bad locus is produced by
`AlgebraicGeometry.ProjectiveSpaceOfModule.exists_isOpen_closedPoint_line_isGood_of_clauseTwo_split`
of `StacksFrontier.AlgebraicGeometry.Intersection.Projections.SingularGoodEndomorphism` out of a
closed subset of `𝐏` carrying the invertible bad classes and of pointwise codimension at least
two. Tag 0B2L part (2c),
`topologicalKrullDimAt_fiber_add_one_le_of_one_le_ringKrullDim_imageClosure` of
`StacksFrontier.AlgebraicGeometry.Variety.FibreDimension`, gets that codimension out of a jump of
the
fibre dimension of `π : T ⟶ 𝐏` above the generic relative dimension `d = dim T - dim Z`, where `Z`
is the reduced closure of the image of `π`. The bound proved here is what makes `d` at most the
expected `dim X + dim Y - dim 𝐏(V)`: with `Z = 𝐏` it reads

`d = dim T - (dim 𝐏) ≤ (dim X + dim Y + (dim V)² - dim V) - ((dim V)² - 1)
   = dim X + dim Y - (dim V - 1)`,

the dimension proper intersection allows for `r_g(X) ∩ Y`. The bound is an inequality in the
direction the codimension argument consumes, and that is the only direction the dimension count of
Tag 0B1R needs too: see
`AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_incidenceVariety_le` of
`StacksFrontier.AlgebraicGeometry.IncidenceDistinctPairs.IncidenceDimension`, of which this file is
the analogue over a base meeting the diagonal.

**No matching lower bound on `dim T` is owed.** It would be, were the bad locus taken to be the
image of the jump locus `{t | dim_t(T_{π t}) ≠ d}` of Tag 0B2L part (2b): the closed points of
that image are bad only if `d` is at least the expected `e = dim X + dim Y - dim 𝐏(V)`, which is
a lower bound on `dim T`. Taking instead the image of

`{t | e + 1 ≤ dim_t(T_{π t})}`,

closed by upper semicontinuity of the local fibre dimension ([Stacks, Tag 02FZ],
`AlgebraicGeometry.isOpen_setOf_fiberDimensionAt_le`), makes both of the conditions that locus is
asked for — that its closed points be bad, and that it contain every invertible bad class — read
off the threshold `e` alone, with no reference to `d`; and the codimension bound then needs only
`d ≤ e`, which is the inequality proved here. That a lower bound on `dim T` would have to be a
statement about the fibre of `T ⟶ 𝐏(V) ×_k 𝐏(V)` over a *non-closed* point, hence about the
subbundle structure and not about the linear subspaces computed here, is what makes the
replacement worth making.

What **is** still owed is that `π` is surjective, that is `Z = 𝐏`. It cannot be dispensed with:
were `Z` a hypersurface and `dim T = dim X + dim Y + (dim V)² - dim V`, the generic relative
dimension would be `d = e + 1`, the generic point of `Z` would be bad, and the bad locus would be
`Z` itself — of codimension one, so the conclusion of Tag 0B1S would fail for that `Z`. By
properness of `π` the image is closed, so surjectivity reduces to `r_g(X) ∩ Y ≠ ∅` for a dense
set of classes `[g]`, and so to the projective dimension theorem (Varieties, Lemma 33.34.3)
applied with `dim X + dim Y ≥ dim 𝐏(V)`. That inequality is where the hypothesis `X ∩ Y ≠ ∅` of
Tag 0B1S enters, since proper intersection bounds `dim (X ∩ Y)` above by
`dim X + dim Y - dim 𝐏(V)` and a nonempty set has dimension at least zero.

## References

* [Stacks Project, Tag 0B1S](https://stacks.math.columbia.edu/tag/0B1S)
* [Stacks Project, Tag 0B2L](https://stacks.math.columbia.edu/tag/0B2L)
* [Stacks Project, Tag 0B2M](https://stacks.math.columbia.edu/tag/0B2M)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

namespace AlgebraicGeometry.ProjectiveSpaceOfModule

universe u

/-- The range of the first projection of a pullback along a rational point is the fibre over it. -/
private theorem range_eq_preimage_of_isPullback {k : Type u} [Field k] {P X S : Scheme.{u}}
    {fst : P ⟶ X} {snd : P ⟶ Spec (CommRingCat.of k)} {f : X ⟶ S} {g : Spec (CommRingCat.of k) ⟶ S}
    (h : IsPullback fst snd f g) {w : S} (hpt : ∀ a, g.base a = w) :
    Set.range fst.base = f.base ⁻¹' {w} := by
  refine Set.Subset.antisymm ?_ ?_
  · rintro _ ⟨q, rfl⟩
    have := congrArg (fun m : P ⟶ S => m.base q) h.w
    simp only [Scheme.Hom.comp_apply] at this
    exact this.trans (hpt _)
  · intro t ht
    obtain ⟨cp⟩ : Nonempty (Spec (CommRingCat.of k)) := ⟨IsLocalRing.closedPoint k⟩
    obtain ⟨z, hz, -⟩ := Scheme.Pullback.exists_preimage_pullback
      (f := f) (g := g) t cp (by rw [hpt]; exact ht)
    refine ⟨h.isoPullback.inv.base z, ?_⟩
    have := congrArg (fun m : pullback f g ⟶ X => m.base z) h.isoPullback_inv_fst
    simp only [Scheme.Hom.comp_apply] at this
    exact this.trans hz

/-- A projection with a section is injective on the range of the section. -/
private theorem injOn_of_range_section {X Y : Scheme.{u}} {s : Y ⟶ X} {p : X ⟶ Y}
    (hsp : s ≫ p = 𝟙 Y) {F : Set X} (hF : Set.range s.base = F) : Set.InjOn p.base F := by
  have hsec : ∀ q, p.base (s.base q) = q := fun q => by
    simpa only [Scheme.Hom.comp_apply, Scheme.Hom.id_base, TopCat.id_app] using
      congrArg (fun m : Y ⟶ Y => m.base q) hsp
  subst hF
  rintro _ ⟨q₁, rfl⟩ _ ⟨q₂, rfl⟩ heq
  rw [hsec, hsec] at heq
  rw [heq]

/-- A closed subset of a quasi-sober space, mapped continuously and injectively into a subset of
a Kolmogorov space, has no larger dimension than that subset. -/
private theorem topologicalKrullDim_le_of_closed_injOn {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] [QuasiSober X] [T0Space Y] {A : Set X} (hA : IsClosed A) {B : Set Y}
    {f : X → Y} (hf : Continuous f) (hAB : ∀ a ∈ A, f a ∈ B) (hinj : Set.InjOn f A) :
    topologicalKrullDim A ≤ topologicalKrullDim B := by
  have : QuasiSober A := Topology.IsClosedEmbedding.quasiSober hA.isClosedEmbedding_subtypeVal
  exact Topology.topologicalKrullDim_le_of_injOn_specializes
    (fun a : A => (⟨f a.1, hAB a.1 a.2⟩ : B)) ((hf.comp continuous_subtype_val).subtype_mk _)
    fun a b _ he => Subtype.ext (hinj a.2 b.2 (congrArg Subtype.val he))

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]
  [IsAlgClosed k] [FiniteDimensional k V] [Nontrivial V]
  [Nontrivial (ParameterModule k V)]

/-! ### The fibre of the ambient triple product over a closed point of the double product -/

/-- **The morphism `[g] ↦ (w, [g])` attached to a closed point `w` of `𝐏(V) ×_k 𝐏(V)`.** Over an
algebraically closed field a closed point is rational, so it is the image of a section
`Spec k ⟶ 𝐏(V) ×_k 𝐏(V)` of the structure morphism, and this is the induced morphism to the
triple product `𝐏(V) ×_k 𝐏(V) ×_k 𝐏`. -/
public def transitionFibreSection {w : prodTwo k V}
    (hw : IsClosed ({w} : Set (prodTwo k V))) :
    projectiveSpaceOfModule k (ParameterModule k V) ⟶ transitionProd k V :=
  pullback.lift
    (projectiveSpaceOfModuleToSpec k (ParameterModule k V) ≫
      pointOfClosedPoint (prodTwoToSpec k V) w hw)
    (𝟙 _)
    (by rw [Category.assoc, pointOfClosedPoint_comp, Category.comp_id, Category.id_comp])

omit [Nontrivial (ParameterModule k V)] in
/-- **`transitionFibreSection` is a section of the projection to the parameter space.** -/
@[reassoc]
public theorem transitionFibreSection_comp_tpPar {w : prodTwo k V}
    (hw : IsClosed ({w} : Set (prodTwo k V))) :
    transitionFibreSection k V hw ≫ tpPar k V = 𝟙 _ :=
  pullback.lift_snd _ _ _

omit [Nontrivial (ParameterModule k V)] in
/-- The composite of `transitionFibreSection` with the projection to the first two factors is the
constant morphism at `w`. -/
@[reassoc]
public theorem transitionFibreSection_comp_tpFst {w : prodTwo k V}
    (hw : IsClosed ({w} : Set (prodTwo k V))) :
    transitionFibreSection k V hw ≫ tpFst k V =
      projectiveSpaceOfModuleToSpec k (ParameterModule k V) ≫
        pointOfClosedPoint (prodTwoToSpec k V) w hw :=
  pullback.lift_fst _ _ _

omit [Nontrivial (ParameterModule k V)] in
/-- **The square formed by `transitionFibreSection` and the rational point `w` is cartesian**: the
fibre of the projection to the first two factors over a rational point of `𝐏(V) ×_k 𝐏(V)` is the
parameter space `𝐏`. It is the square defining the triple product, with the trivial square of the
identity of `Spec k` pasted on its right. -/
public theorem isPullback_transitionFibreSection {w : prodTwo k V}
    (hw : IsClosed ({w} : Set (prodTwo k V))) :
    IsPullback (transitionFibreSection k V hw)
      (projectiveSpaceOfModuleToSpec k (ParameterModule k V)) (tpFst k V)
      (pointOfClosedPoint (prodTwoToSpec k V) w hw) := by
  refine IsPullback.of_right (h₁₂ := tpPar k V) ?_ (transitionFibreSection_comp_tpFst k V hw)
    (IsPullback.of_hasPullback (prodTwoToSpec k V)
      (projectiveSpaceOfModuleToSpec k (ParameterModule k V))).flip
  rw [transitionFibreSection_comp_tpPar, pointOfClosedPoint_comp]
  exact IsPullback.of_id_fst

omit [Nontrivial (ParameterModule k V)] in
/-- **The range of `transitionFibreSection` is the set-theoretic fibre of `tpFst` over `w`.** -/
public theorem range_transitionFibreSection {w : prodTwo k V}
    (hw : IsClosed ({w} : Set (prodTwo k V))) :
    Set.range (transitionFibreSection k V hw).base = (tpFst k V).base ⁻¹' {w} := by
  exact range_eq_preimage_of_isPullback (isPullback_transitionFibreSection k V hw)
    (pointOfClosedPoint_apply (prodTwoToSpec k V) w hw)

omit [Nontrivial (ParameterModule k V)] in
/-- **The projection to the parameter space is injective on the fibre of `tpFst` over a closed
point.** It has a section there, `transitionFibreSection`. -/
public theorem injOn_tpPar_fibre {w : prodTwo k V}
    (hw : IsClosed ({w} : Set (prodTwo k V))) :
    Set.InjOn (tpPar k V).base ((tpFst k V).base ⁻¹' {w}) := by
  exact injOn_of_range_section (transitionFibreSection_comp_tpPar k V hw)
    (range_transitionFibreSection k V hw)

/-! ### The fibre of the ambient triple product over a closed point of the parameter space -/

/-- **The morphism `(x, y) ↦ (x, y, [g])` attached to a closed point `q` of the parameter space
`𝐏`.** This is the section of the projection to the first two factors over `q`, the mirror of
`AlgebraicGeometry.ProjectiveSpaceOfModule.transitionFibreSection`. -/
public def parFibreSection {q : projectiveSpaceOfModule k (ParameterModule k V)}
    (hq : IsClosed ({q} : Set (projectiveSpaceOfModule k (ParameterModule k V)))) :
    prodTwo k V ⟶ transitionProd k V :=
  pullback.lift (𝟙 _)
    (prodTwoToSpec k V ≫
      pointOfClosedPoint (projectiveSpaceOfModuleToSpec k (ParameterModule k V)) q hq)
    (by rw [Category.id_comp, Category.assoc, pointOfClosedPoint_comp, Category.comp_id])

omit [Nontrivial V] in
/-- **`parFibreSection` is a section of the projection to the first two factors.** -/
@[reassoc]
public theorem parFibreSection_comp_tpFst
    {q : projectiveSpaceOfModule k (ParameterModule k V)}
    (hq : IsClosed ({q} : Set (projectiveSpaceOfModule k (ParameterModule k V)))) :
    parFibreSection k V hq ≫ tpFst k V = 𝟙 _ :=
  pullback.lift_fst _ _ _

omit [Nontrivial V] in
/-- The composite of `parFibreSection` with the projection to the parameter space is the constant
morphism at `q`. -/
@[reassoc]
public theorem parFibreSection_comp_tpPar
    {q : projectiveSpaceOfModule k (ParameterModule k V)}
    (hq : IsClosed ({q} : Set (projectiveSpaceOfModule k (ParameterModule k V)))) :
    parFibreSection k V hq ≫ tpPar k V =
      prodTwoToSpec k V ≫
        pointOfClosedPoint (projectiveSpaceOfModuleToSpec k (ParameterModule k V)) q hq :=
  pullback.lift_snd _ _ _

omit [Nontrivial V] in
/-- **The square formed by `parFibreSection` and the rational point `q` is cartesian**: the fibre
of the projection to the parameter space over a rational point of `𝐏` is `𝐏(V) ×_k 𝐏(V)`. -/
public theorem isPullback_parFibreSection
    {q : projectiveSpaceOfModule k (ParameterModule k V)}
    (hq : IsClosed ({q} : Set (projectiveSpaceOfModule k (ParameterModule k V)))) :
    IsPullback (parFibreSection k V hq) (prodTwoToSpec k V) (tpPar k V)
      (pointOfClosedPoint (projectiveSpaceOfModuleToSpec k (ParameterModule k V)) q hq) := by
  refine IsPullback.of_right (h₁₂ := tpFst k V) ?_ (parFibreSection_comp_tpPar k V hq)
    (IsPullback.of_hasPullback (prodTwoToSpec k V)
      (projectiveSpaceOfModuleToSpec k (ParameterModule k V)))
  rw [parFibreSection_comp_tpFst, pointOfClosedPoint_comp]
  exact IsPullback.of_id_fst

omit [Nontrivial V] in
/-- **The range of `parFibreSection` is the set-theoretic fibre of `tpPar` over `q`.** -/
public theorem range_parFibreSection {q : projectiveSpaceOfModule k (ParameterModule k V)}
    (hq : IsClosed ({q} : Set (projectiveSpaceOfModule k (ParameterModule k V)))) :
    Set.range (parFibreSection k V hq).base = (tpPar k V).base ⁻¹' {q} := by
  exact range_eq_preimage_of_isPullback (isPullback_parFibreSection k V hq)
    (pointOfClosedPoint_apply (projectiveSpaceOfModuleToSpec k (ParameterModule k V)) q hq)

omit [Nontrivial V] in
/-- **The projection to the first two factors is injective on the fibre of `tpPar` over a closed
point.** It has a section there, `parFibreSection`. This is what reduces the fibre of the
incidence correspondence over a class `[g]` to a closed subset of `𝐏(V) ×_k 𝐏(V)` — the graph of
`r_g` over `X ∩ r_g⁻¹(Y)`, once the transition equations are read on it. -/
public theorem injOn_tpFst_parFibre {q : projectiveSpaceOfModule k (ParameterModule k V)}
    (hq : IsClosed ({q} : Set (projectiveSpaceOfModule k (ParameterModule k V)))) :
    Set.InjOn (tpFst k V).base ((tpPar k V).base ⁻¹' {q}) := by
  exact injOn_of_range_section (parFibreSection_comp_tpFst k V hq)
    (range_parFibreSection k V hq)

/-! ### Finite-type instances for the projections -/

public instance locallyOfFiniteType_tpFst : LocallyOfFiniteType (tpFst k V) :=
  MorphismProperty.of_isPullback
    (IsPullback.of_hasPullback (prodTwoToSpec k V)
      (projectiveSpaceOfModuleToSpec k (ParameterModule k V))).flip inferInstance

public instance locallyOfFiniteType_tpPar : LocallyOfFiniteType (tpPar k V) :=
  MorphismProperty.of_isPullback
    (IsPullback.of_hasPullback (prodTwoToSpec k V)
      (projectiveSpaceOfModuleToSpec k (ParameterModule k V))) inferInstance

public instance locallyOfFiniteType_transitionProj : LocallyOfFiniteType (transitionProj k V) :=
  inferInstanceAs (LocallyOfFiniteType (transitionSubschemeι k V ≫ tpFst k V))

public instance locallyOfFiniteType_transitionVarietyToBase {S : Scheme.{u}}
    (f : S ⟶ prodTwo k V) : LocallyOfFiniteType (transitionVarietyToBase k V f) :=
  MorphismProperty.of_isPullback (IsPullback.of_hasPullback (transitionProj k V) f) inferInstance

/-! ### The dimension bound on the fibre -/

/-- **The transition locus over a closed point of `𝐏(V) ×_k 𝐏(V)` has dimension at most
`(dim V)² - dim V`.** The parameter projection is injective on the fibre of `tpFst`, and it
carries the transition locus over the pair `([f], [f'])` into the projective linear subspace cut
out by `AlgebraicGeometry.ProjectiveSpaceOfModule.transitionEquations`, whose dimension is that
number. The containment is checked at the closed points of the fibre — the only points at which
the minor sections of `𝒪(1,1,1)` can be evaluated — and transported to the whole of it by
`Set.subset_of_isClosed_of_closedPoints_subset`.

As in
`AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_linearSubspace_transitionEquations`
the number is pinned without subtraction: `m` is fixed by `dim_k (End V)ᵛ = m + dim_k V`. -/
public theorem topologicalKrullDim_transitionLocus_inter_le {n m : ℕ}
    (hV : Module.finrank k V = n + 1)
    (hm : Module.finrank k (ParameterModule k V) = m + n + 1)
    {w : prodTwo k V} (hw : IsClosed ({w} : Set (prodTwo k V))) :
    topologicalKrullDim
        ((transitionLocus k V ∩ (tpFst k V).base ⁻¹' {w} : Set (transitionProd k V))) ≤
      (m : WithBot ℕ∞) := by
  have : JacobsonSpace (projectiveSpaceOfModule k V) :=
    LocallyOfFiniteType.jacobsonSpace (projectiveSpaceOfModuleToSpec k V)
  have : JacobsonSpace (projectiveSpaceOfModule k (ParameterModule k V)) :=
    LocallyOfFiniteType.jacobsonSpace (projectiveSpaceOfModuleToSpec k (ParameterModule k V))
  have : JacobsonSpace (transitionProd k V) :=
    LocallyOfFiniteType.jacobsonSpace (transitionProdToSpec k V)
  set y := (pullback.fst (projectiveSpaceOfModuleToSpec k V)
    (projectiveSpaceOfModuleToSpec k V)).base w with hy
  set z := (pullback.snd (projectiveSpaceOfModuleToSpec k V)
    (projectiveSpaceOfModuleToSpec k V)).base w with hz
  have hyc : IsClosed ({y} : Set (projectiveSpaceOfModule k V)) :=
    (pullback.fst (projectiveSpaceOfModuleToSpec k V)
      (projectiveSpaceOfModuleToSpec k V)).closedPoints_subset_preimage_closedPoints hw
  have hzc : IsClosed ({z} : Set (projectiveSpaceOfModule k V)) :=
    (pullback.snd (projectiveSpaceOfModuleToSpec k V)
      (projectiveSpaceOfModuleToSpec k V)).closedPoints_subset_preimage_closedPoints hw
  obtain ⟨f, hf, hfy⟩ := exists_eq_linearFunctionalPoint k V y hyc
  obtain ⟨f', hf', hf'z⟩ := exists_eq_linearFunctionalPoint k V z hzc
  set L : Set (projectiveSpaceOfModule k (ParameterModule k V)) :=
    linearSubspace k (ParameterModule k V) (transitionEquations k V f f') with hL
  have hLdim : topologicalKrullDim L = (m : WithBot ℕ∞) :=
    topologicalKrullDim_linearSubspace_transitionEquations k V hV hm hf hf'
  set A : Set (transitionProd k V) :=
    transitionLocus k V ∩ (tpFst k V).base ⁻¹' {w} with hA
  have hAclosed : IsClosed A :=
    (isClosed_transitionLocus k V).inter (hw.preimage (Scheme.Hom.continuous (tpFst k V)))
  -- the parameter projection of every point of `A` lies on the linear subspace
  have hsub : A ⊆ (tpPar k V).base ⁻¹' L := by
    refine Set.subset_of_isClosed_of_closedPoints_subset hAclosed
      ((isClosed_linearSubspace k (ParameterModule k V) _).preimage
        (Scheme.Hom.continuous (tpPar k V))) (fun t ht htc => ?_)
    -- the two points of the pair are the projections of `t`
    have hsrc : (tpSource k V).base t = linearFunctionalPoint k V f hf := by
      have h : (tpSource k V).base t = (pullback.fst (projectiveSpaceOfModuleToSpec k V)
          (projectiveSpaceOfModuleToSpec k V)).base ((tpFst k V).base t) := rfl
      rw [h, ht.2, ← hy, ← hfy]
    have htgt : (tpTarget k V).base t = linearFunctionalPoint k V f' hf' := by
      have h : (tpTarget k V).base t = (pullback.snd (projectiveSpaceOfModuleToSpec k V)
          (projectiveSpaceOfModuleToSpec k V)).base ((tpFst k V).base t) := rfl
      rw [h, ht.2, ← hz, ← hf'z]
    -- the parameter projection of `t` is a closed point, hence cut out by a functional
    have hparc : IsClosed ({(tpPar k V).base t} :
        Set (projectiveSpaceOfModule k (ParameterModule k V))) :=
      (tpPar k V).closedPoints_subset_preimage_closedPoints htc
    obtain ⟨f₃, hf₃, hpar⟩ :=
      exists_eq_linearFunctionalPoint k (ParameterModule k V) ((tpPar k V).base t) hparc
    -- the endomorphism that functional names
    set g := (Module.evalEquiv k (V →ₗ[k] V)).symm f₃ with hgdef
    have hgval : ∀ ψ : ParameterModule k V, f₃ ψ = ψ g := fun ψ =>
      (Module.apply_evalEquiv_symm_apply k (V →ₗ[k] V) ψ f₃).symm
    have hspan : f ∘ₗ g ∈ Submodule.span k {f'} :=
      (mem_transitionLocus_iff_of_linearFunctionalPoint k V t f hf hsrc f' hf' htgt f₃ hf₃
        hpar g hgval).mp ht.1
    rw [Set.mem_preimage, hL, hpar, mem_linearSubspace_iff,
      pointSubmodule_linearFunctionalPoint k (ParameterModule k V) f₃ hf₃]
    intro φ hφ
    rw [LinearMap.mem_ker, hgval φ]
    exact (forall_apply_eq_zero_transitionEquations_iff k V f f' g).mpr hspan φ hφ
  -- `A` is closed, and the parameter projection injects it into the subspace
  exact (topologicalKrullDim_le_of_closed_injOn hAclosed (Scheme.Hom.continuous (tpPar k V))
    (fun t ht => hsub ht) ((injOn_tpPar_fibre k V hw).mono fun t ht => ht.2)).trans_eq hLdim

/-- **The fibre of the projection of the incidence correspondence to `𝐏(V) ×_k 𝐏(V)` over a closed
point has dimension at most `(dim V)² - dim V`.** This is the fibre bound of Tag 0B1S: the fibre
is the projective linear subspace of classes carrying the first point of the pair to the second,
and — unlike for the incidence variety of lines of Tag 0B1R — it is of that dimension over *every*
pair, the diagonal included. -/
public theorem topologicalKrullDim_fiber_transitionProj_le {n m : ℕ}
    (hV : Module.finrank k V = n + 1)
    (hm : Module.finrank k (ParameterModule k V) = m + n + 1)
    {w : prodTwo k V} (hw : IsClosed ({w} : Set (prodTwo k V))) :
    topologicalKrullDim ((transitionProj k V).fiber w) ≤ (m : WithBot ℕ∞) := by
  refine topologicalKrullDim_fiber_le_of_preimage_subset (transitionProj k V) w
    ((transitionProj k V).base ⁻¹' {w}) subset_rfl ?_
  have hemb : Topology.IsClosedEmbedding (transitionSubschemeι k V).base :=
    IsClosedImmersion.isClosedEmbedding (transitionSubschemeι k V)
  set Z : Set (transitionSubscheme k V) := (transitionProj k V).base ⁻¹' {w} with hZ
  set A : Set (transitionProd k V) :=
    transitionLocus k V ∩ (tpFst k V).base ⁻¹' {w} with hA
  have hmap : ∀ c ∈ Z, (transitionSubschemeι k V).base c ∈ A := by
    intro c hc
    refine ⟨(range_transitionSubschemeι k V).subset (Set.mem_range_self c), ?_⟩
    have h : (tpFst k V).base ((transitionSubschemeι k V).base c) =
        (transitionProj k V).base c := rfl
    rw [Set.mem_preimage, h]
    exact hc
  exact (topologicalKrullDim_le_of_closed_injOn
    (hw.preimage (Scheme.Hom.continuous (transitionProj k V)))
    (Scheme.Hom.continuous (transitionSubschemeι k V)) (fun c hc => hmap c hc)
    hemb.injective.injOn).trans (topologicalKrullDim_transitionLocus_inter_le k V hV hm hw)

/-! ### The relative dimension of the correspondence over a product of closed subvarieties -/

variable (X Y : Set (projectiveSpaceOfModule k V)) (hXc : IsClosed X) (hYc : IsClosed Y)

/-- **The incidence correspondence of Tag 0B1S over the product of two closed subvarieties has
relative dimension at most `(dim V)² - dim V` over that base.** Over a closed point of the base the
fibre is the projective linear subspace of classes carrying the first point to the second, of that
dimension; the bound at every point of the source follows by upper semicontinuity of the local
fibre dimension.

This is the input the dimension count of Tag 0B1S consumes: together with the dimension of the
base (`AlgebraicGeometry.ProjectiveSpaceOfModule.topologicalKrullDim_prodOfClosed`, which is Tag
0B2M) it bounds the dimension of the correspondence by `dim X + dim Y + (dim V)² - dim V`. -/
public theorem relativeDimensionLE_transitionVarietyToBase {n m : ℕ}
    (hV : Module.finrank k V = n + 1)
    (hm : Module.finrank k (ParameterModule k V) = m + n + 1) :
    RelativeDimensionLE
      (transitionVarietyToBase k V (prodOfClosedToProdTwo k V X Y hXc hYc)) m := by
  set f := prodOfClosedToProdTwo k V X Y hXc hYc with hfdef
  have : LocallyOfFiniteType f :=
    locallyOfFiniteType_prodOfClosedToProdTwo k V X Y hXc hYc
  have : JacobsonSpace (prodTwo k V) :=
    LocallyOfFiniteType.jacobsonSpace (prodTwoToSpec k V)
  have : JacobsonSpace (transitionVariety k V f) :=
    LocallyOfFiniteType.jacobsonSpace
      (transitionVarietyToBase k V f ≫ f ≫ prodTwoToSpec k V)
  intro x
  refine fiberDimensionAt_le_of_isClosed_singleton (transitionVarietyToBase k V f)
    (fun t ht => ?_) x
  have hsq := isPullback_transitionVariety k V f
  have hbase : (transitionProj k V).base ((transitionVarietyToSubscheme k V f).base t) =
      f.base ((transitionVarietyToBase k V f).base t) := by
    have h := congrArg (fun m : transitionVariety k V f ⟶ prodTwo k V => m.base t) hsq.w
    simpa only [Scheme.Hom.comp_apply] using h
  have hwclosed : IsClosed ({f.base ((transitionVarietyToBase k V f).base t)} :
      Set (prodTwo k V)) := by
    have h : (transitionVarietyToBase k V f ≫ f).base t ∈ closedPoints (prodTwo k V) :=
      (transitionVarietyToBase k V f ≫ f).closedPoints_subset_preimage_closedPoints ht
    rw [Scheme.Hom.comp_apply] at h
    exact h
  rw [topologicalKrullDimAt_fiber_eq_of_isPullback hsq t]
  refine le_trans (topologicalKrullDimAt_le_topologicalKrullDim _) ?_
  rw [hbase]
  exact topologicalKrullDim_fiber_transitionProj_le k V hV hm hwclosed

/-- **The incidence correspondence of Tag 0B1S over `X × Y` has dimension at most
`dim X + dim Y + (dim V)² - dim V`.** The projection to the base has relative dimension at most
`(dim V)² - dim V`, and the base has dimension `dim X + dim Y`.

This is the upper bound the codimension argument of Tag 0B1S needs: it makes the generic relative
dimension of `π : T ⟶ 𝐏` at most `dim X + dim Y - dim 𝐏(V)`, the dimension proper intersection
allows for `r_g(X) ∩ Y`. -/
public theorem topologicalKrullDim_transitionVariety_le {n m : ℕ}
    (hV : Module.finrank k V = n + 1)
    (hm : Module.finrank k (ParameterModule k V) = m + n + 1) :
    topologicalKrullDim (transitionVariety k V (prodOfClosedToProdTwo k V X Y hXc hYc)) ≤
      topologicalKrullDim ↥X + topologicalKrullDim ↥Y + (m : WithBot ℕ∞) := by
  set f := prodOfClosedToProdTwo k V X Y hXc hYc with hfdef
  have : LocallyOfFiniteType f :=
    locallyOfFiniteType_prodOfClosedToProdTwo k V X Y hXc hYc
  set pB : (prodOfClosed k V X Y hXc hYc) ⟶ Spec (.of k) := f ≫ prodTwoToSpec k V with hpB
  have : LocallyOfFiniteType pB := by rw [hpB]; infer_instance
  set q := transitionVarietyToBase k V f with hq
  have : LocallyOfFiniteType q := by rw [hq]; infer_instance
  have hrel := relativeDimensionLE_transitionVarietyToBase k V X Y hXc hYc hV hm
  rw [topologicalKrullDim_eq_iSup_localKrullDim]
  refine iSup_le fun x => ?_
  rw [← topologicalKrullDimAt_eq_localKrullDim]
  refine le_trans (topologicalKrullDimAt_le_fiber_add_topologicalKrullDimAt_target k
    (q ≫ pB) pB q rfl x) ?_
  have h1 : topologicalKrullDimAt (q.fiber (q.base x)) (q.asFiber x) ≤ (m : WithBot ℕ∞) := by
    have := hrel x
    rw [relativeDimensionLEAt_iff] at this
    simpa using this
  have h2 : topologicalKrullDimAt (prodOfClosed k V X Y hXc hYc) (q.base x) ≤
      topologicalKrullDim ↥X + topologicalKrullDim ↥Y :=
    le_trans (topologicalKrullDimAt_le_topologicalKrullDim _)
      (le_of_eq (topologicalKrullDim_prodOfClosed k V X Y hXc hYc))
  refine le_trans (add_le_add h1 h2) (le_of_eq ?_)
  rw [add_comm]

end AlgebraicGeometry.ProjectiveSpaceOfModule

end
