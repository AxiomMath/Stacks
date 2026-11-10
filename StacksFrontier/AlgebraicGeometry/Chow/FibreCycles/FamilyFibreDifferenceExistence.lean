module

public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.FibreFamilyReduction
public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.FibreDifferencePushforward
public import StacksFrontier.AlgebraicGeometry.Chow.UniversalPrincipalDivisorCycles.AmbientFibreDifference
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.ComponentPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.PreparationProperPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasicoherentSubobjectGluing.FiniteTypeCover

/-!
# Every cycle rationally equivalent to zero is a family of fibre differences

Let `f : X ⟶ S` be locally of finite type over the base of a Chow situation and let `α` be a
`k`-cycle on `X` which is rationally equivalent to zero. By definition that means `α` is,
coefficient by coefficient, a locally finite sum of pushforwards of principal divisors
`div_{V_j}(g_j)` of rational functions on integral closed subschemes `V_j ⊆ X` of
delta-dimension `k + 1`.

This file produces from that data a locally finite family of integral closed subschemes of
`X ×_S 𝐏¹_S`, each of relative dimension `k + 1` and contained in neither distinguished
section, whose total zero-minus-infinity fibre difference is `α`. That is the converse
direction of Stacks Tag 02S4 part (3), namely **part (4)** of that tag.

The construction is the graph construction of Tag 02RQ, applied one member at a time. A
rational function on an integral scheme is an invertible section on some affine open — the
closure of the graph of the attached morphism to `𝐏¹_S` is the subscheme wanted, and part (6)
of Tag 02RQ already says that its two fibres, read as closed subschemes of `V_j`, have
difference the principal divisor of the function. What this file adds is the transport of that
statement from `V_j ×_S 𝐏¹_S` to `X ×_S 𝐏¹_S` along the closed immersion induced by
`V_j ⟶ X`, and the three side conditions of part (3): integrality, the relative dimension at
the generic points, and non-degeneracy with respect to the two sections.

## Main definitions

* `Stacks.Chow.familyBaseChange` — the closed immersion `Y ×_S 𝐏¹_S ⟶ X ×_S 𝐏¹_S` induced by a
  closed immersion `Y ⟶ X`.
* `Stacks.Chow.graphFamilyMember` — the closed subscheme of `X ×_S 𝐏¹_S` attached to an
  integral closed subscheme of `X` together with an invertible section on an open of it: the
  image of the graph closure of Tag 02RQ.

## Main results

* `Stacks.Chow.exists_unit_section` — a unit of the ring of rational functions of an integral
  scheme is represented by an invertible section on an affine dense open.
* `Stacks.Chow.zeroFiber_graphFamilyMember` and
  `Stacks.Chow.infinityFiber_graphFamilyMember` — the two fibres of that subscheme are the
  two fibres of the graph closure, pushed into `X`.
* `Stacks.Chow.principalDivisorPushforward_eq_sub_fibreCycles` — the pushforward of the
  principal divisor is the difference of the two fibre cycles of that subscheme.
* `Stacks.Chow.exists_familyFibreDifferences` — **Stacks Tag 02S4, part (4).**

## Implementation notes

The induced map on families is stated as an `IsPullback` square
(`Stacks.Chow.isPullback_familyBaseChange`) rather than through the universal property of the
pullback cone, and so is its compatibility with the constant sections
(`Stacks.Chow.isPullback_constantSection_familyBaseChange`); every subsequent statement about
kernels and fibres is then a rewrite with
`AlgebraicGeometry.ker_eq_comap_ker_of_isPullback` and no induced isomorphism is ever
composed.

Non-degeneracy is checked at the generic point of the graph closure, which is where Tag 02RQ
already knows the answer: `Stacks.Chow.notMem_support_graphZeroFiber_genericPoint` says the
generic point does not lie on the zero fibre. It is therefore not necessary to know that the
fibre is an effective Cartier divisor, nor to use the delta-dimension of the graph closure for
this step.

Local finiteness is inherited rather than recomputed: the support of the new member lies in
the preimage of the support of the old one under the projection `X ×_S 𝐏¹_S ⟶ X`, and the
preimage of a locally finite family under a continuous map is locally finite.

The family in the conclusion is indexed by the same type as the family witnessing rational
equivalence, so no reindexing is needed.

## References

* [Stacks Project, Tag 02S4](https://stacks.math.columbia.edu/tag/02S4)
* [Stacks Project, Tag 02RQ](https://stacks.math.columbia.edu/tag/02RQ)
* [Stacks Project, Tag 02RW](https://stacks.math.columbia.edu/tag/02RW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### The image of a section, as a preimage from the projective line -/

/-- The image of the zero section of `X ×_S 𝐏¹_S ⟶ X` is the preimage of `D₀ ⊆ 𝐏¹_S` under the
second projection. -/
theorem range_zeroSection_eq_preimage {X S : Scheme.{u}} (f : X ⟶ S) :
    Set.range (zeroSection f) =
      pullback.snd f (relativeProjectiveLine S ↘ S) ⁻¹' Set.range (lineZeroSection S) := by
  have h := Scheme.Hom.support_ker (zeroSection f)
  rw [ker_zeroSection, Scheme.IdealSheafData.support_comap] at h
  rw [← (isClosed_range_zeroSection f).closure_eq, ← h, Closeds.coe_preimage,
    coe_support_lineZeroDivisor]

/-- The image of the infinity section of `X ×_S 𝐏¹_S ⟶ X` is the preimage of `D_∞ ⊆ 𝐏¹_S`
under the second projection. -/
theorem range_infinitySection_eq_preimage {X S : Scheme.{u}} (f : X ⟶ S) :
    Set.range (infinitySection f) =
      pullback.snd f (relativeProjectiveLine S ↘ S) ⁻¹' Set.range (lineInfinitySection S) := by
  have h := Scheme.Hom.support_ker (infinitySection f)
  rw [ker_infinitySection, Scheme.IdealSheafData.support_comap] at h
  rw [← (isClosed_range_infinitySection f).closure_eq, ← h, Closeds.coe_preimage,
    coe_support_lineInfinityDivisor]

/-! ### The family of projective lines over a closed subscheme -/

/-- The morphism `Y ×_S 𝐏¹_S ⟶ X ×_S 𝐏¹_S` induced by a morphism `i : Y ⟶ X`. -/
def familyBaseChange {X Y S : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X) :
    projectiveLineProduct (i ≫ f) ⟶ projectiveLineProduct f :=
  pullback.lift (pullback.fst (i ≫ f) (relativeProjectiveLine S ↘ S) ≫ i)
    (pullback.snd (i ≫ f) (relativeProjectiveLine S ↘ S))
    (by rw [Category.assoc, pullback.condition])

section BaseChange

variable {X Y S : Scheme.{u}} (f : X ⟶ S) (i : Y ⟶ X)

/-- The induced morphism on families commutes with the first projections and `i`. -/
@[simp]
theorem familyBaseChange_comp_fst :
    familyBaseChange f i ≫ pullback.fst f (relativeProjectiveLine S ↘ S) =
      pullback.fst (i ≫ f) (relativeProjectiveLine S ↘ S) ≫ i :=
  pullback.lift_fst _ _ _

/-- The induced morphism on families commutes with the second projections to `𝐏¹_S`. -/
@[simp]
theorem familyBaseChange_comp_snd :
    familyBaseChange f i ≫ pullback.snd f (relativeProjectiveLine S ↘ S) =
      pullback.snd (i ≫ f) (relativeProjectiveLine S ↘ S) :=
  pullback.lift_snd _ _ _

/-- The induced morphism on families is a base change of `i` along the first projection. -/
theorem isPullback_familyBaseChange :
    IsPullback (pullback.fst (i ≫ f) (relativeProjectiveLine S ↘ S)) (familyBaseChange f i) i
      (pullback.fst f (relativeProjectiveLine S ↘ S)) := by
  refine IsPullback.of_bot (v₂₁ := pullback.snd f (relativeProjectiveLine S ↘ S)) (v₂₂ := f)
    ?_ ?_ (IsPullback.of_hasPullback f (relativeProjectiveLine S ↘ S))
  · simpa only [familyBaseChange_comp_snd] using
      IsPullback.of_hasPullback (i ≫ f) (relativeProjectiveLine S ↘ S)
  · simp

/-- The morphism on families induced by a closed immersion is a closed immersion. -/
instance isClosedImmersion_familyBaseChange [IsClosedImmersion i] :
    IsClosedImmersion (familyBaseChange f i) :=
  MorphismProperty.of_isPullback (isPullback_familyBaseChange f i) inferInstance

/-- The constant sections are compatible with the morphism induced on families. -/
theorem constantSection_comp_familyBaseChange
    (e : (⊤_ Scheme.{u}) ⟶ projectiveLine (ULift.{u} ℤ)) :
    constantSection (i ≫ f) e ≫ familyBaseChange f i = i ≫ constantSection f e := by
  refine pullback.hom_ext ?_ ?_
  · simp only [familyBaseChange, constantSection, Category.assoc, pullback.lift_fst,
      pullback.lift_fst_assoc, Category.id_comp, Category.comp_id]
  · simp only [familyBaseChange, constantSection, Category.assoc, pullback.lift_snd]
    refine pullback.hom_ext ?_ ?_ <;>
      simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, terminal.comp_from_assoc]

/-- The constant section of the family over `Y` is the base change of the constant section of
the family over `X` along the induced morphism. -/
theorem isPullback_constantSection_familyBaseChange [IsClosedImmersion i]
    (e : (⊤_ Scheme.{u}) ⟶ projectiveLine (ULift.{u} ℤ)) :
    IsPullback (constantSection (i ≫ f) e) i (familyBaseChange f i) (constantSection f e) := by
  refine IsPullback.of_right (h₁₂ := pullback.fst (i ≫ f) (relativeProjectiveLine S ↘ S))
    (h₂₂ := pullback.fst f (relativeProjectiveLine S ↘ S)) (v₁₃ := i) ?_ ?_
    (isPullback_familyBaseChange f i)
  · simpa only [constantSection_comp_fst] using IsPullback.id_horiz i
  · exact constantSection_comp_familyBaseChange f i e

/-! ### A rational function comes from an invertible section on an affine dense open -/

/-- A unit of the ring of rational functions of an integral scheme is the rational function of
an invertible section on an affine open, which is automatically dense. -/
theorem exists_unit_section (Z : Scheme.{u}) [IsIntegral Z] (g : (rationalFunctions Z)ˣ) :
    ∃ (U : Z.Opens) (_ : IsAffineOpen U) (hU : Dense (U : Set Z)) (s : (Γ(Z, U))ˣ),
      ofSection Z ⟨U, hU⟩ (s : Γ(Z, U)) = (g : rationalFunctions Z) := by
  set e := (rationalFunctionsEquivFunctionField Z).1 with he
  have hne : e (g : rationalFunctions Z) ≠ 0 := (g.isUnit.map e.toRingHom).ne_zero
  obtain ⟨U, hUaff, s, hUne, hs, t, rfl⟩ :=
    AlgebraicGeometry.exists_isUnit_germ_eq Z (e (g : rationalFunctions Z)) hne
  have hd : Dense (U : Set Z) := U.isOpen.dense (Set.nonempty_coe_sort.mp hUne)
  refine ⟨U, hUaff, hd, t, e.injective ?_⟩
  rw [(rationalFunctionsEquivFunctionField Z).2 ⟨U, hd⟩ (t : Γ(Z, U))
    ((genericPoint_spec Z).mem_open_set_iff U.isOpen |>.mpr (by simpa using hUne))]
  exact hs

/-! ### The fibres of the image of a closed subscheme of the family -/

/-- The fibre over a section of the first projection of the image of a closed subscheme `Z` of
`X ×_S 𝐏¹_S` is the image in `X` of the fibre over that section computed on `Z`. -/
theorem comap_ker_section_eq_map {Z : Scheme.{u}} (σ : X ⟶ projectiveLineProduct f)
    [IsClosedImmersion σ] (hσ : σ ≫ pullback.fst f (relativeProjectiveLine S ↘ S) = 𝟙 X)
    (j : Z ⟶ projectiveLineProduct f) [IsClosedImmersion j] :
    (Scheme.Hom.ker j).comap σ =
      ((Scheme.Hom.ker σ).comap j).map
        (j ≫ pullback.fst f (relativeProjectiveLine S ↘ S)) := by
  rw [← Scheme.IdealSheafData.ker_fst_of_isClosedImmersion σ j, Scheme.IdealSheafData.map_ker]
  have he : pullback.fst j σ ≫ (j ≫ pullback.fst f (relativeProjectiveLine S ↘ S)) =
      pullback.snd j σ := by
    rw [← Category.assoc, pullback.condition, Category.assoc, hσ, Category.comp_id]
  rw [he]
  exact (ker_eq_comap_ker_of_isPullback (IsPullback.of_hasPullback j σ).flip).symm

/-! ### The graph closure, read inside the family over the ambient scheme -/

section Graph

variable (U : Y.Opens) (s : Γ(Y, U))

/-- The closed immersion of the graph closure of a section on an open of a closed subscheme
`Y ⊆ X` into the family `X ×_S 𝐏¹_S` over the ambient scheme. -/
def graphFamilyInclusion : graphClosure (i ≫ f) U s ⟶ projectiveLineProduct f :=
  graphClosureι (i ≫ f) U s ≫ familyBaseChange f i

/-- Projecting the graph closure to `X` is projecting it to `Y` and then including. -/
theorem graphFamilyInclusion_comp_fst :
    graphFamilyInclusion f i U s ≫ pullback.fst f (relativeProjectiveLine S ↘ S) =
      graphProjection (i ≫ f) U s ≫ i := by
  rw [graphFamilyInclusion, Category.assoc, familyBaseChange_comp_fst]
  exact (Category.assoc _ _ _).symm

/-- Projecting the graph closure to `𝐏¹_S` does not see the ambient scheme. -/
theorem graphFamilyInclusion_comp_snd :
    graphFamilyInclusion f i U s ≫ pullback.snd f (relativeProjectiveLine S ↘ S) =
      graphLineProjection (i ≫ f) U s := by
  rw [graphFamilyInclusion, Category.assoc, familyBaseChange_comp_snd]

variable [IsClosedImmersion i]

/-- The inclusion of the graph closure into `X ×_S 𝐏¹_S` is a closed immersion. -/
instance isClosedImmersion_graphFamilyInclusion :
    IsClosedImmersion (graphFamilyInclusion f i U s) :=
  inferInstanceAs (IsClosedImmersion (_ ≫ familyBaseChange f i))

/-- The closed subscheme of `X ×_S 𝐏¹_S` cut out by the graph closure: the member of the family
of Stacks 02S4 part (4) attached to one integral closed subscheme and one section. -/
def graphFamilyMember : (projectiveLineProduct f).IdealSheafData :=
  Scheme.Hom.ker (graphFamilyInclusion f i U s)

/-- The support of the member is the image of the graph closure. -/
theorem range_graphFamilyMember_subschemeι :
    Set.range (graphFamilyMember f i U s).subschemeι =
      Set.range (graphFamilyInclusion f i U s) := by
  rw [Scheme.IdealSheafData.range_subschemeι, graphFamilyMember, Scheme.Hom.support_ker]
  exact (IsClosedImmersion.isClosedEmbedding
    (graphFamilyInclusion f i U s)).isClosed_range.closure_eq

/-- The member is integral when the graph closure is: a closed immersion is an isomorphism onto
the subscheme it cuts out. -/
theorem isIntegral_graphFamilyMember [IsIntegral (graphClosure (i ≫ f) U s)] :
    IsIntegral (graphFamilyMember f i U s).subscheme := by
  have h2 : IsIso (Scheme.Hom.toImage (graphFamilyInclusion f i U s)) := inferInstance
  exact @IsIntegral.of_isIso _ _ ‹_› (Scheme.Hom.toImage (graphFamilyInclusion f i U s)) h2

/-- **The zero fibre of the member is the zero fibre of the graph closure, read in `X`.** -/
theorem zeroFiber_graphFamilyMember :
    zeroFiber f (graphFamilyMember f i U s) =
      (graphZeroFiber (i ≫ f) U s).map (graphProjection (i ≫ f) U s ≫ i) := by
  rw [zeroFiber, graphFamilyMember,
    comap_ker_section_eq_map f (zeroSection f) (zeroSection_comp_fst f)
      (graphFamilyInclusion f i U s),
    ker_zeroSection, ← Scheme.IdealSheafData.comap_comp,
    graphFamilyInclusion_comp_fst, graphFamilyInclusion_comp_snd]
  rfl

/-- **The infinity fibre of the member is the infinity fibre of the graph closure, read in
`X`.** -/
theorem infinityFiber_graphFamilyMember :
    infinityFiber f (graphFamilyMember f i U s) =
      (graphInfinityFiber (i ≫ f) U s).map (graphProjection (i ≫ f) U s ≫ i) := by
  rw [infinityFiber, graphFamilyMember,
    comap_ker_section_eq_map f (infinitySection f) (infinitySection_comp_fst f)
      (graphFamilyInclusion f i U s),
    ker_infinitySection, ← Scheme.IdealSheafData.comap_comp,
    graphFamilyInclusion_comp_fst, graphFamilyInclusion_comp_snd]
  rfl

omit [IsClosedImmersion i] in
/-- The graph closure factors through the closed subscheme of `X ×_S 𝐏¹_S` that it cuts out. -/
theorem toImage_comp_graphFamilyMember_subschemeι :
    (graphFamilyInclusion f i U s).toImage ≫ (graphFamilyMember f i U s).subschemeι =
      graphFamilyInclusion f i U s :=
  Scheme.Hom.toImage_imageι _

/-- The support of the member lies over the ambient closed subscheme: the projection of the
graph closure factors through `Y`. -/
theorem support_graphFamilyMember_subset :
    ((graphFamilyMember f i U s).support : Set (projectiveLineProduct f)) ⊆
      pullback.fst f (relativeProjectiveLine S ↘ S) ⁻¹' Set.range i := by
  rw [← Scheme.IdealSheafData.range_subschemeι, range_graphFamilyMember_subschemeι]
  rintro _ ⟨y, rfl⟩
  refine ⟨graphProjection (i ≫ f) U s y, ?_⟩
  simpa only [Scheme.Hom.comp_apply] using
    congrArg (fun q : graphClosure (i ≫ f) U s ⟶ X => q.base y)
      (graphFamilyInclusion_comp_fst f i U s).symm

/-- The member lies in the image of a section `σ`, the preimage of a set `T ⊆ 𝐏¹_S`, only if the
generic point of the graph closure maps into `T`. -/
private theorem not_subset_range_graphFamilyMember {σ : X ⟶ projectiveLineProduct f}
    {T : Set (relativeProjectiveLine S)} [IsIntegral (graphClosure (i ≫ f) U s)]
    (hσ : Set.range σ = pullback.snd f (relativeProjectiveLine S ↘ S) ⁻¹' T)
    (h : genericPoint (graphClosure (i ≫ f) U s) ∉
      graphLineProjection (i ≫ f) U s ⁻¹' T) :
    ¬ Set.range (graphFamilyMember f i U s).subschemeι ⊆ Set.range σ := by
  intro hsub
  refine h ?_
  have hmem := hsub (show graphFamilyInclusion f i U s
      (genericPoint (graphClosure (i ≫ f) U s)) ∈ _ by
    rw [range_graphFamilyMember_subschemeι]
    exact Set.mem_range_self _)
  rw [hσ, Set.mem_preimage] at hmem
  rw [Set.mem_preimage, ← graphFamilyInclusion_comp_snd f i U s]
  simpa only [Scheme.Hom.comp_apply] using hmem

end Graph
/-! ### The member meets neither distinguished section -/

section Nondegenerate

variable [IsClosedImmersion i] [IsIntegral Y] (U : Y.Opens) [QuasiCompact U.ι]
  [Nonempty U.toScheme] (g : (Γ(Y, U))ˣ)
  [IsIntegral (graphClosure (i ≫ f) U (g : Γ(Y, U)))]

/-- **The member is not contained in the image of the zero section.** Its generic point is the
image of the generic point of the graph closure, which Tag 02RQ puts off the zero fibre. -/
theorem notSubset_range_zeroSection_graphFamilyMember :
    ¬ Set.range (graphFamilyMember f i U (g : Γ(Y, U))).subschemeι ⊆
      Set.range (zeroSection f) :=
  not_subset_range_graphFamilyMember f i U (g : Γ(Y, U)) (range_zeroSection_eq_preimage f)
    (by
      rw [← coe_support_graphZeroFiber]
      exact notMem_support_graphZeroFiber_genericPoint (i ≫ f) U g)

/-- **The member is not contained in the image of the infinity section.** -/
theorem notSubset_range_infinitySection_graphFamilyMember :
    ¬ Set.range (graphFamilyMember f i U (g : Γ(Y, U))).subschemeι ⊆
      Set.range (infinitySection f) :=
  not_subset_range_graphFamilyMember f i U (g : Γ(Y, U)) (range_infinitySection_eq_preimage f)
    (by
      rw [← coe_support_graphInfinityFiber]
      exact notMem_support_graphInfinityFiber_genericPoint (i ≫ f) U g)

end Nondegenerate

end BaseChange
/-! ### The relative dimension and the fibre cycles of the member -/

section ChowSituation

variable (C : ChowSituation.{u}) {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f]
  {Y : Scheme.{u}} (i : Y ⟶ X) [IsClosedImmersion i] (U : Y.Opens) (s : Γ(Y, U))

/-- **The delta-dimension of the member equals that of the ambient closed subscheme.** The
member is isomorphic to the graph closure, whose delta-dimension Tag 02RQ computes. -/
theorem schemeDeltaDimension_familyBase_graphFamilyMember [IsIntegral Y] [QuasiCompact U.ι]
    (g : (Γ(Y, U))ˣ) (hU : Dense (U : Set Y)) {n : ℤ}
    (hn : schemeDeltaDimension C (i ≫ f) = (n : EInt)) :
    schemeDeltaDimension C (familyBase f (graphFamilyMember f i U (g : Γ(Y, U)))) =
      (n : EInt) := by
  have hYint : IsIntegral (graphClosure (i ≫ f) U (g : Γ(Y, U))) :=
    isIntegral_graphClosure (i ≫ f) U (g : Γ(Y, U)) hU
  have hYft : LocallyOfFiniteType (graphBaseMorphism (i ≫ f) U (g : Γ(Y, U))) :=
    locallyOfFiniteType_graphBaseMorphism (i ≫ f) U (g : Γ(Y, U))
  have : IsIntegral (graphFamilyMember f i U (g : Γ(Y, U))).subscheme :=
    isIntegral_graphFamilyMember f i U (g : Γ(Y, U))
  have hIso : IsIso (Scheme.Hom.toImage (graphFamilyInclusion f i U (g : Γ(Y, U)))) :=
    inferInstance
  have hfac : (@asIso _ _ _ _ (Scheme.Hom.toImage
        (graphFamilyInclusion f i U (g : Γ(Y, U)))) hIso).hom ≫
      familyBase f (graphFamilyMember f i U (g : Γ(Y, U))) =
      graphBaseMorphism (i ≫ f) U (g : Γ(Y, U)) := by
    rw [asIso_hom]
    calc Scheme.Hom.toImage (graphFamilyInclusion f i U (g : Γ(Y, U))) ≫
          familyBase f (graphFamilyMember f i U (g : Γ(Y, U)))
        = (Scheme.Hom.toImage (graphFamilyInclusion f i U (g : Γ(Y, U))) ≫
            (graphFamilyMember f i U (g : Γ(Y, U))).subschemeι) ≫
            (pullback.fst f (relativeProjectiveLine C.S ↘ C.S) ≫ f) :=
          (Category.assoc _ _ _).symm
      _ = graphFamilyInclusion f i U (g : Γ(Y, U)) ≫
            (pullback.fst f (relativeProjectiveLine C.S ↘ C.S) ≫ f) := by
          rw [toImage_comp_graphFamilyMember_subschemeι]
      _ = (graphFamilyInclusion f i U (g : Γ(Y, U)) ≫
            pullback.fst f (relativeProjectiveLine C.S ↘ C.S)) ≫ f := (Category.assoc _ _ _).symm
      _ = (graphProjection (i ≫ f) U (g : Γ(Y, U)) ≫ i) ≫ f := by
          rw [graphFamilyInclusion_comp_fst]
      _ = graphBaseMorphism (i ≫ f) U (g : Γ(Y, U)) := Category.assoc _ _ _
  rw [schemeDeltaDimension_of_iso C (graphBaseMorphism (i ≫ f) U (g : Γ(Y, U)))
    (familyBase f (graphFamilyMember f i U (g : Γ(Y, U)))) _ hfac]
  exact schemeDeltaDimension_graphClosure C (i ≫ f) U g n hn hU hYft

/-- **The dimension hypothesis of Stacks 02S4 part (3), for the member.** -/
theorem relativeDimension_familyBase_graphFamilyMember [IsIntegral Y] [QuasiCompact U.ι]
    (g : (Γ(Y, U))ˣ) (hU : Dense (U : Set Y)) {n : ℤ}
    (hn : schemeDeltaDimension C (i ≫ f) = (n : EInt))
    (ξ : genericPoints (graphFamilyMember f i U (g : Γ(Y, U))).subscheme) :
    relativeDimension C.dimensionFunction
      (familyBase f (graphFamilyMember f i U (g : Γ(Y, U)))) ξ.1 = n := by
  have hYint : IsIntegral (graphClosure (i ≫ f) U (g : Γ(Y, U))) :=
    isIntegral_graphClosure (i ≫ f) U (g : Γ(Y, U)) hU
  have : IsIntegral (graphFamilyMember f i U (g : Γ(Y, U))).subscheme :=
    isIntegral_graphFamilyMember f i U (g : Γ(Y, U))
  have hξ : ξ.1 = genericPoint (graphFamilyMember f i U (g : Γ(Y, U))).subscheme := by
    simpa only [genericPoints_eq_singleton, Set.mem_singleton_iff] using ξ.2
  have hgen := schemeDeltaDimension_eq_genericPoint C
    (familyBase f (graphFamilyMember f i U (g : Γ(Y, U))))
  rw [schemeDeltaDimension_familyBase_graphFamilyMember C f i U g hU hn] at hgen
  rw [hξ]
  exact (WithBotTop.coe_injective hgen).symm

/-- The cycle of a closed subscheme of `Y'` pushed along `h₁ ≫ i` is that of the closed subscheme
given by the image ideal sheaf. -/
private theorem cycleAssociatedToClosedSubscheme_comp_eq_of_map_eq (C : ChowSituation.{u})
    {X : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] {Y Y' : Scheme.{u}} (i : Y ⟶ X)
    [IsClosedImmersion i] (h₁ : Y' ⟶ Y) (J : Y'.IdealSheafData)
    [IsClosedImmersion (J.subschemeι ≫ h₁)] (I : X.IdealSheafData) (hI : J.map (h₁ ≫ i) = I)
    (k : ℤ) :
    cycleAssociatedToClosedSubscheme C f ((J.subschemeι ≫ h₁) ≫ i) k =
      cycleAssociatedToClosedSubscheme C f I.subschemeι k := by
  rw [cycleAssociatedToClosedSubscheme_ker C f, ← hI, Category.assoc]
  rfl

/-- The cycle of the zero fibre of the member is the cycle of the zero fibre of the graph
closure, read as a closed subscheme of `X`. -/
theorem cycleAssociatedToClosedSubscheme_zeroFiber_graphFamilyMember (k : ℤ)
    [IsClosedImmersion ((graphZeroFiber (i ≫ f) U s).subschemeι ≫
      graphProjection (i ≫ f) U s)] :
    cycleAssociatedToClosedSubscheme C f
        (((graphZeroFiber (i ≫ f) U s).subschemeι ≫ graphProjection (i ≫ f) U s) ≫ i) k =
      cycleAssociatedToClosedSubscheme C f
        (zeroFiber f (graphFamilyMember f i U s)).subschemeι k :=
  cycleAssociatedToClosedSubscheme_comp_eq_of_map_eq C f i _ _ _
    (zeroFiber_graphFamilyMember f i U s).symm k

/-- The cycle of the infinity fibre of the member is the cycle of the infinity fibre of the
graph closure, read as a closed subscheme of `X`. -/
theorem cycleAssociatedToClosedSubscheme_infinityFiber_graphFamilyMember (k : ℤ)
    [IsClosedImmersion ((graphInfinityFiber (i ≫ f) U s).subschemeι ≫
      graphProjection (i ≫ f) U s)] :
    cycleAssociatedToClosedSubscheme C f
        (((graphInfinityFiber (i ≫ f) U s).subschemeι ≫ graphProjection (i ≫ f) U s) ≫ i) k =
      cycleAssociatedToClosedSubscheme C f
        (infinityFiber f (graphFamilyMember f i U s)).subschemeι k :=
  cycleAssociatedToClosedSubscheme_comp_eq_of_map_eq C f i _ _ _
    (infinityFiber_graphFamilyMember f i U s).symm k

/-! ### The principal divisor of a rational function as a fibre difference -/

/-- **The pushforward of the principal divisor of a rational function on an integral closed
subscheme `V ⊆ X` is the fibre difference of the graph member.**

Part (6) of Tag 02RQ gives the identity on `V`, where the two fibres of the graph closure are
closed subschemes of `V`; proper pushforward along the closed immersion `V ⟶ X` carries it to
`X`, and the two fibres of the member are exactly the images of those two. -/
theorem principalDivisorPushforward_eq_sub_fibreCycles (k : ℤ) (V : X.IdealSheafData)
    (hV : IsIntegral V.subscheme)
    (hdim : schemeDeltaDimension C (V.subschemeι ≫ f) = ((k + 1 : ℤ) : EInt))
    (g : (rationalFunctions V.subscheme)ˣ) (U : V.subscheme.Opens) [QuasiCompact U.ι]
    (hU : Dense (U : Set V.subscheme)) (t : (Γ(V.subscheme, U))ˣ)
    (ht : ofSection V.subscheme ⟨U, hU⟩ (t : Γ(V.subscheme, U)) =
      (g : rationalFunctions V.subscheme)) :
    principalDivisorPushforward C f V hV g =
      (cycleAssociatedToClosedSubscheme C f
          (zeroFiber f (graphFamilyMember f V.subschemeι U (t : Γ(V.subscheme, U)))).subschemeι
          k).1 -
        (cycleAssociatedToClosedSubscheme C f
          (infinityFiber f
            (graphFamilyMember f V.subschemeι U (t : Γ(V.subscheme, U)))).subschemeι k).1 := by
  have hVint : IsIntegral V.subscheme := hV
  have : IsLocallyNoetherian V.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (V.subschemeι ≫ f)
  have h₀ : IsClosedImmersion ((graphZeroFiber (V.subschemeι ≫ f) U
      (t : Γ(V.subscheme, U))).subschemeι ≫
      graphProjection (V.subschemeι ≫ f) U (t : Γ(V.subscheme, U))) :=
    isClosedImmersion_graphZeroFiber_comp (V.subschemeι ≫ f) U (t : Γ(V.subscheme, U))
  have hInf : IsClosedImmersion ((graphInfinityFiber (V.subschemeι ≫ f) U
      (t : Γ(V.subscheme, U))).subschemeι ≫
      graphProjection (V.subschemeι ≫ f) U (t : Γ(V.subscheme, U))) :=
    isClosedImmersion_graphInfinityFiber_comp (V.subschemeι ≫ f) U (t : Γ(V.subscheme, U))
  have hk : (k + 1 - 1 : ℤ) = k := by ring
  have h6' : principalCycle V.subscheme
        ((rationalFunctionsEquivFunctionField V.subscheme).1
          (g : rationalFunctions V.subscheme)) =
      (cycleAssociatedToClosedSubscheme C (V.subschemeι ≫ f)
          ((graphZeroFiber (V.subschemeι ≫ f) U (t : Γ(V.subscheme, U))).subschemeι ≫
            graphProjection (V.subschemeι ≫ f) U (t : Γ(V.subscheme, U))) (k + 1 - 1)).1 -
        (cycleAssociatedToClosedSubscheme C (V.subschemeι ≫ f)
          ((graphInfinityFiber (V.subschemeι ≫ f) U (t : Γ(V.subscheme, U))).subschemeι ≫
            graphProjection (V.subschemeι ≫ f) U (t : Γ(V.subscheme, U))) (k + 1 - 1)).1 := by
    have h := congrArg Subtype.val
      (principalDivisorCycle_eq_sub_imageCycles C (V.subschemeι ≫ f) U t (k + 1) hdim g hU ht
        h₀ hInf)
    rw [AddSubgroup.coe_sub] at h
    exact h
  rw [hk] at h6'
  have hmem : principalCycle V.subscheme
      ((rationalFunctionsEquivFunctionField V.subscheme).1
        (g : rationalFunctions V.subscheme)) ∈
      cyclesOfDimension C (V.subschemeι ≫ f) k := by
    have h := principalCycle_mem_cyclesOfDimension C (V.subschemeι ≫ f) hdim
      ((rationalFunctionsEquivFunctionField V.subscheme).1 (g : rationalFunctions V.subscheme))
    rwa [hk] at h
  have hc : (⟨_, hmem⟩ : CycleGroup C (V.subschemeι ≫ f) k) =
      cycleAssociatedToClosedSubscheme C (V.subschemeι ≫ f)
          ((graphZeroFiber (V.subschemeι ≫ f) U (t : Γ(V.subscheme, U))).subschemeι ≫
            graphProjection (V.subschemeι ≫ f) U (t : Γ(V.subscheme, U))) k -
        cycleAssociatedToClosedSubscheme C (V.subschemeι ≫ f)
          ((graphInfinityFiber (V.subschemeι ≫ f) U (t : Γ(V.subscheme, U))).subschemeι ≫
            graphProjection (V.subschemeι ≫ f) U (t : Γ(V.subscheme, U))) k := by
    refine Subtype.ext ?_
    rw [AddSubgroup.coe_sub]
    exact h6'
  have hpush := congrArg Subtype.val
    (congrArg (properPushforward C (V.subschemeι ≫ f) f V.subschemeι rfl k) hc)
  rw [properPushforward_sub,
    properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp C
      (V.subschemeι ≫ f) f V.subschemeι rfl
      ((graphZeroFiber (V.subschemeι ≫ f) U (t : Γ(V.subscheme, U))).subschemeι ≫
        graphProjection (V.subschemeι ≫ f) U (t : Γ(V.subscheme, U))) k,
    properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp C
      (V.subschemeι ≫ f) f V.subschemeι rfl
      ((graphInfinityFiber (V.subschemeι ≫ f) U (t : Γ(V.subscheme, U))).subschemeι ≫
        graphProjection (V.subschemeι ≫ f) U (t : Γ(V.subscheme, U))) k,
    cycleAssociatedToClosedSubscheme_zeroFiber_graphFamilyMember C f V.subschemeι U
      (t : Γ(V.subscheme, U)) k,
    cycleAssociatedToClosedSubscheme_infinityFiber_graphFamilyMember C f V.subschemeι U
      (t : Γ(V.subscheme, U)) k, AddSubgroup.coe_sub] at hpush
  exact hpush

/-! ### Stacks 02S4, part (4) -/

/-- One member of the family of Stacks 02S4 part (4): from an integral closed subscheme
`V ⊆ X` of delta-dimension `k + 1` and a rational function on it, the graph closure gives a
closed subscheme of `X ×_S 𝐏¹_S` with all the properties part (3) asks of a family member and
with fibre difference the pushforward of the principal divisor. -/
theorem exists_graphFamilyMember (k : ℤ) (V : X.IdealSheafData) (hV : IsIntegral V.subscheme)
    (hdim : schemeDeltaDimension C (V.subschemeι ≫ f) = ((k + 1 : ℤ) : EInt))
    (g : (rationalFunctions V.subscheme)ˣ) :
    ∃ W : (projectiveLineProduct f).IdealSheafData,
      IsIntegral W.subscheme ∧
      (∀ ξ : genericPoints W.subscheme,
        relativeDimension C.dimensionFunction (familyBase f W) ξ.1 = k + 1) ∧
      ¬ Set.range W.subschemeι ⊆ Set.range (zeroSection f) ∧
      ¬ Set.range W.subschemeι ⊆ Set.range (infinitySection f) ∧
      ((W.support : Set (projectiveLineProduct f)) ⊆
        pullback.fst f (relativeProjectiveLine C.S ↘ C.S) ⁻¹' (V.support : Set X)) ∧
      (∀ x : X, principalDivisorPushforward C f V hV g x =
        (cycleAssociatedToClosedSubscheme C f (zeroFiber f W).subschemeι k).1 x -
          (cycleAssociatedToClosedSubscheme C f (infinityFiber f W).subschemeι k).1 x) := by
  have hVint : IsIntegral V.subscheme := hV
  have hLN : IsLocallyNoetherian V.subscheme :=
    LocallyOfFiniteType.isLocallyNoetherian (V.subschemeι ≫ f)
  obtain ⟨U, hUaff, hU, t, ht⟩ := exists_unit_section V.subscheme g
  have hqc : QuasiCompact U.ι :=
    AlgebraicGeometry.quasiCompact_ι_of_isCompact U hUaff.isCompact
  have hne : Nonempty U.toScheme := Set.nonempty_coe_sort.mpr hU.nonempty
  have hYint : IsIntegral (graphClosure (V.subschemeι ≫ f) U (t : Γ(V.subscheme, U))) :=
    isIntegral_graphClosure (V.subschemeι ≫ f) U (t : Γ(V.subscheme, U)) hU
  refine ⟨graphFamilyMember f V.subschemeι U (t : Γ(V.subscheme, U)),
    isIntegral_graphFamilyMember f V.subschemeι U (t : Γ(V.subscheme, U)),
    fun ξ ↦ relativeDimension_familyBase_graphFamilyMember C f V.subschemeι U t hU hdim ξ,
    notSubset_range_zeroSection_graphFamilyMember f V.subschemeι U t,
    notSubset_range_infinitySection_graphFamilyMember f V.subschemeι U t, ?_, fun x ↦ ?_⟩
  · refine (support_graphFamilyMember_subset f V.subschemeι U (t : Γ(V.subscheme, U))).trans ?_
    rw [V.range_subschemeι]
  · have h := principalDivisorPushforward_eq_sub_fibreCycles C f k V hV hdim g U hU t ht
    simpa using congrArg (fun c : AlgebraicCycle X ℤ => c x) h

/-- **Stacks Project, Tag 02S4, part (4).** A `k`-cycle rationally equivalent to zero is the
total fibre difference of a locally finite family of integral closed subschemes of
`X ×_S 𝐏¹_S`, each of relative dimension `k + 1` at its generic points and contained in
neither distinguished section.

This is the converse of part (3): the family is produced from the family of integral closed
subschemes and rational functions witnessing rational equivalence, by replacing each member by
the closure of the graph of its rational function, read inside `X ×_S 𝐏¹_S`. The index type is
unchanged. -/
@[stacks 02S4 "part (4)"]
theorem exists_familyFibreDifferences (k : ℤ) (α : CycleGroup C f k)
    (hα : IsRationallyEquivalentToZero C f k α) :
    ∃ (J : Type u) (W : J → (projectiveLineProduct f).IdealSheafData),
      (∀ j, IsIntegral (W j).subscheme) ∧
      (∀ j, ∀ ξ : genericPoints (W j).subscheme,
        relativeDimension C.dimensionFunction (familyBase f (W j)) ξ.1 = k + 1) ∧
      (∀ j, ¬ Set.range (W j).subschemeι ⊆ Set.range (zeroSection f)) ∧
      (∀ j, ¬ Set.range (W j).subschemeι ⊆ Set.range (infinitySection f)) ∧
      LocallyFinite (fun j ↦ ((W j).support : Set (projectiveLineProduct f))) ∧
      (∀ x : X, α.1 x = familyFibreDifferenceCoefficient C f k W x) := by
  obtain ⟨J, V, hV, hdim, hLocal, g, hg⟩ := hα
  choose W hWint hWdim hW₀ hWInf hWsupp hWcoeff using
    fun j ↦ exists_graphFamilyMember C f k (V j) (hV j) (hdim j) (g j)
  refine ⟨J, W, hWint, hWdim, hW₀, hWInf, ?_, fun x ↦ ?_⟩
  · exact LocallyFinite.subset
      (hLocal.preimage_continuous
        (pullback.fst f (relativeProjectiveLine C.S ↘ C.S)).continuous) hWsupp
  · rw [hg x, principalDivisorFamilyCoefficient, familyFibreDifferenceCoefficient]
    exact finsum_congr fun j ↦ hWcoeff j x

end ChowSituation

end Stacks.Chow

end
