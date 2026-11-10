module

public import Mathlib.AlgebraicGeometry.Fiber
public import StacksFrontier.AlgebraicGeometry.Algebraization.DepthInequalities
public import StacksFrontier.AlgebraicGeometry.Algebraization.DistanceFiniteType
public import StacksFrontier.AlgebraicGeometry.Algebraization.DistanceOpenRestriction
public import StacksFrontier.AlgebraicGeometry.Algebraization.DistanceSpecialization
public import StacksFrontier.AlgebraicGeometry.Algebraization.DistanceSublevel
public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleDominating
public import StacksFrontier.AlgebraicGeometry.CartierQuotientChart.Basic
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.AffineChartAlgebraization
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.BlowupAlgebraizationCharts
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionCriteria.AffineExistence

/-!
# The distance function on the exceptional divisor in the proof of Stacks 0EJK

In Situation [Stacks, Tag 0EHC] let `b : X' ⟶ X` be the blowup of `X = Spec(A)` in `I`, let
`Y' ⊆ X'` be the exceptional divisor and `Z' ⊆ Y'` the inverse image of `Z ⊆ Y`. The proof of
[Stacks, Tag 0EJK] uses the distance function `δ^{Y'}_{Z'}` of [Stacks, Tag 0EIX] on `Y'`. This
file sets up the morphism `Y' ⟶ Y` (the restriction of `b`), the closed subset `Z'`, and the two
comparisons the proof makes:

* [Stacks, Tag 0EIZ] for `Y' ⟶ Y`: `δ^Y_Z(b(y')) + trdeg_{κ(b(y'))} κ(y') ≤ δ^{Y'}_{Z'}(y') + e`
  when the fibres of `b` over the points of `Y` have dimension at most `e`
  (`Stacks.Algebraization.distanceToZ_add_trdeg_le_exceptional`);
* [Stacks, Tag 0EIY] part (6) for the chart `Spec(Γ(V)/I(V)) ⟶ Y'` of an affine open `V ⊆ X'`:
  the distance function of the algebraization situation of `V` is at least `δ^{Y'}_{Z'}`
  (`Stacks.Algebraization.exceptionalDistance_le_chartDistance`).

## Main definitions

* `Stacks.Algebraization.situationExceptional` — the exceptional divisor `Y'`.
* `Stacks.Algebraization.exceptionalToY` — the morphism `Y' ⟶ Y`.
* `Stacks.Algebraization.exceptionalZ` — the closed subset `Z' = Y' ∖ U'` of `Y'`.
* `Stacks.Algebraization.exceptionalDistance` — `δ^{Y'}_{Z'}`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Algebraization

variable (S : AlgebraizationSituation.{u})

/-- The exceptional divisor `Y' = V(I𝒪_{X'})` of the blowup. -/
abbrev situationExceptional : Scheme.{u} := (situationExceptionalIdeal S).subscheme

/-- The closed immersion `Y' ⟶ X'`. -/
abbrev situationExceptionalι : situationExceptional S ⟶ situationBlowUp S :=
  (situationExceptionalIdeal S).subschemeι

/-- The open `U' = b⁻¹(U)` of the blowup. -/
abbrev situationBlowUpU : (situationBlowUp S).Opens := situationBlowUpToBase S ⁻¹ᵁ S.U

/-- The exceptional divisor `Y'` is a Noetherian scheme. -/
instance isNoetherian_situationExceptional : IsNoetherian (situationExceptional S) := by
  have := isNoetherian_situationBlowUp S
  have : IsLocallyNoetherian (situationExceptional S) :=
    LocallyOfFiniteType.isLocallyNoetherian (situationExceptionalι S)
  have : CompactSpace (situationExceptional S) :=
    QuasiCompact.compactSpace_of_compactSpace (situationExceptionalι S)
  exact {}

/-- The ideal of `Y ⊆ X` is contained in the kernel of the composite `Y' ⟶ X' ⟶ X`. -/
theorem ker_Yι_le_ker_exceptional :
    S.Yι.ker ≤ (situationExceptionalι S ≫ situationBlowUpToBase S).ker := by
  rw [Scheme.Hom.ker_comp, Scheme.IdealSheafData.ker_subschemeι, ker_Yι_eq_ofIdealTop]
  exact Scheme.IdealSheafData.le_map_comap (Stacks.LocalCohomology.specIdealSheaf S.A S.I) _

/-- The restriction `Y' ⟶ Y` of the blowup morphism to the exceptional divisor. -/
def exceptionalToY : situationExceptional S ⟶ S.Y :=
  IsClosedImmersion.lift S.Yι _ (ker_Yι_le_ker_exceptional S)

/-- The composite `Y' ⟶ Y ⟶ X` equals the composite `Y' ⟶ X' ⟶ X`. -/
@[reassoc]
theorem exceptionalToY_Yι :
    exceptionalToY S ≫ S.Yι = situationExceptionalι S ≫ situationBlowUpToBase S :=
  IsClosedImmersion.lift_fac _ _ _

/-- The morphism `Y' ⟶ Y` is locally of finite type. -/
instance : LocallyOfFiniteType (exceptionalToY S) := by
  have : LocallyOfFiniteType (exceptionalToY S ≫ S.Yι) := by
    rw [exceptionalToY_Yι]
    infer_instance
  exact LocallyOfFiniteType.of_comp this

/-- The morphism `Y' ⟶ Y` is quasi-compact. -/
instance : QuasiCompact (exceptionalToY S) := by
  have : QuasiCompact (exceptionalToY S ≫ S.Yι) := by
    rw [exceptionalToY_Yι]
    infer_instance
  exact QuasiCompact.of_comp (exceptionalToY S) S.Yι

/-- The ideal of `Z = V(𝔞)` inside `Y = Spec(A/I)`. -/
abbrev zIdealOnY : S.Y.IdealSheafData :=
  Stacks.LocalCohomology.specIdealSheaf (S.A ⧸ S.I) (S.a.map (Ideal.Quotient.mk S.I))

/-- The support of the ideal of `Z` on `Y` is the closed subset `Z`. -/
theorem support_zIdealOnY : (zIdealOnY S).support = S.closedSubsetZ :=
  Closeds.ext (Stacks.LocalCohomology.coe_support_specIdealSheaf _ _)

/-- The closed subset `Z' ⊆ Y'`, the inverse image of `Z ⊆ Y`. -/
abbrev exceptionalZ : Closeds (situationExceptional S) :=
  ((zIdealOnY S).comap (exceptionalToY S)).support

/-- The distance function `δ^{Y'}_{Z'}` on the exceptional divisor. -/
abbrev exceptionalDistance (x : situationExceptional S) : ℕ∞ :=
  distanceFunction (situationExceptional S) (exceptionalZ S) x

/-- A point of `Y` lies in `Z` exactly when its image in `X` does not lie in `U`. -/
theorem mem_closedSubsetZ_iff (z : S.Y) :
    z ∈ (S.closedSubsetZ : Set S.Y) ↔ S.Yι z ∉ S.U := by
  change ((S.a.map (Ideal.Quotient.mk S.I) : Ideal (S.A ⧸ S.I)) : Set (S.A ⧸ S.I)) ⊆
      ((z : PrimeSpectrum (S.A ⧸ S.I)).asIdeal : Set (S.A ⧸ S.I)) ↔
    ¬¬ ((S.a : Set S.A) ⊆
      (Ideal.comap (Ideal.Quotient.mk S.I) (z : PrimeSpectrum (S.A ⧸ S.I)).asIdeal : Set S.A))
  rw [not_not, SetLike.coe_subset_coe, SetLike.coe_subset_coe, Ideal.map_le_iff_le_comap]

/-- A point lies in the support of the pullback of an ideal sheaf iff its image lies in the
support. -/
private theorem mem_support_comap_iff {X Y : Scheme.{u}} (f : X ⟶ Y) (I : Y.IdealSheafData)
    (x : X) : x ∈ (I.comap f).support ↔ f x ∈ I.support := by
  rw [Scheme.IdealSheafData.support_comap]
  rfl

/-- **A point of `Y'` lies in `Z'` exactly when it does not lie in `U'`.** -/
theorem mem_exceptionalZ_iff (x : situationExceptional S) :
    x ∈ exceptionalZ S ↔ situationExceptionalι S x ∉ situationBlowUpU S := by
  rw [exceptionalZ, mem_support_comap_iff, support_zIdealOnY,
    ← SetLike.mem_coe, mem_closedSubsetZ_iff]
  change ¬ (exceptionalToY S ≫ S.Yι) x ∈ S.U ↔
    ¬ (situationExceptionalι S ≫ situationBlowUpToBase S) x ∈ S.U
  rw [exceptionalToY_Yι]

/-- **[Stacks, Tag 0EIZ] for `Y' ⟶ Y`.** If `Y` is universally catenary and the fibres of
`Y' ⟶ Y` have dimension at most `e`, then
`δ^Y_Z(y) + trdeg_{κ(y)} κ(y') ≤ δ^{Y'}_{Z'}(y') + e` for `y'` over `y`. -/
theorem distanceToZ_add_trdeg_le_exceptional (hcat : Scheme.IsUniversallyCatenary S.Y) (e : ℕ)
    (he : ∀ y : S.Y, topologicalKrullDim ((exceptionalToY S).fiber y) ≤ (e : WithBot ℕ∞))
    (x : situationExceptional S) :
    letI := ((exceptionalToY S).residueFieldMap x).hom.toAlgebra
    S.distanceToZ (exceptionalToY S x) +
        Cardinal.toENat (Algebra.trdeg (S.Y.residueField (exceptionalToY S x))
          ((situationExceptional S).residueField x)) ≤
      exceptionalDistance S x + (e : ℕ∞) := by
  have h := distanceFunction_add_trdeg_le (exceptionalToY S) hcat (zIdealOnY S) e he x
  rwa [support_zIdealOnY] at h

/-- The complement of `U'` lies in the exceptional divisor. -/
theorem compl_situationBlowUpU_subset :
    ((situationBlowUpU S : Set (situationBlowUp S)))ᶜ ⊆ (situationExceptionalIdeal S).support := by
  intro x hx
  change x ∈ ((Stacks.LocalCohomology.specIdealSheaf S.A S.I).comap
    (situationBlowUpToBase S)).support
  rw [mem_support_comap_iff]
  change situationBlowUpToBase S x ∈
    ((Stacks.LocalCohomology.specIdealSheaf S.A S.I).support : Set S.X)
  rw [Stacks.LocalCohomology.coe_support_specIdealSheaf]
  have hx' : situationBlowUpToBase S x ∉ S.U := hx
  change ¬ _ ∈ (PrimeSpectrum.zeroLocus (S.a : Set S.A))ᶜ at hx'
  exact PrimeSpectrum.zeroLocus_anti_mono S.I_le_a (not_not.mp hx')

variable (V : (situationBlowUp S).affineOpens)

/-- The image in `X'` of a point of the chart `Spec(Γ(V)/I(V))` of `Y'`. -/
theorem situationExceptionalι_subschemeCover (z : (chartSituation (situationExceptionalIdeal S)
      (situationBlowUpU S) V (compl_situationBlowUpU_subset S)).Y) :
    situationExceptionalι S ((situationExceptionalIdeal S).subschemeCover.f V z) =
      chartFromSpec (situationExceptionalIdeal S) (situationBlowUpU S) V
        (compl_situationBlowUpU_subset S)
        ((chartSituation (situationExceptionalIdeal S) (situationBlowUpU S) V
          (compl_situationBlowUpU_subset S)).Yι z) := by
  change ((situationExceptionalIdeal S).subschemeCover.f V ≫ situationExceptionalι S) z = _
  rw [← Stacks.CartierQuotientChart.quotientImmersion_ι (situationExceptionalIdeal S) V]
  simp only [Stacks.CartierQuotientChart.quotientImmersion, chartFromSpec, IsAffineOpen.fromSpec]
  rfl

/-- **[Stacks, Tag 0EIY] part (6) for an affine chart of `Y'`.** The distance function of the
algebraization situation of an affine open `V ⊆ X'` is at least `δ^{Y'}_{Z'}`. -/
theorem exceptionalDistance_le_chartDistance (z : (chartSituation (situationExceptionalIdeal S)
      (situationBlowUpU S) V (compl_situationBlowUpU_subset S)).Y) :
    exceptionalDistance S ((situationExceptionalIdeal S).subschemeCover.f V z) ≤
      (chartSituation (situationExceptionalIdeal S) (situationBlowUpU S) V
        (compl_situationBlowUpU_subset S)).distanceToZ z := by
  have : IsOpenImmersion ((situationExceptionalIdeal S).subschemeCover.f V) :=
    (situationExceptionalIdeal S).subschemeCover.map_prop V
  refine (distanceFunction_le_of_isOpenImmersion
    ((situationExceptionalIdeal S).subschemeCover.f V) (exceptionalZ S) z).trans_eq ?_
  unfold AlgebraizationSituation.distanceToZ
  congr 1
  refine Closeds.ext (Set.ext fun (w : (chartSituation (situationExceptionalIdeal S)
    (situationBlowUpU S) V (compl_situationBlowUpU_subset S)).Y) => ?_)
  refine (mem_exceptionalZ_iff S _).trans ?_
  rw [situationExceptionalι_subschemeCover]
  refine (not_congr ?_).trans (mem_closedSubsetZ_iff _ w).symm
  rw [chartSituation_U (situationExceptionalIdeal S) (situationBlowUpU S) V
    (compl_situationBlowUpU_subset S)]
  rfl

/-- **The fibres of `Y' ⟶ Y` are no bigger than those of the blowup.** The fibre of `Y' ⟶ Y`
over `y` embeds into the fibre of `b : X' ⟶ X` over the image of `y`; the blowup is read here in
the model `AlgebraicGeometry.blowUp`, through `Stacks.Blowup.blowUpIso`. -/
theorem topologicalKrullDim_fiber_exceptionalToY_le (y : S.Y) :
    topologicalKrullDim ((exceptionalToY S).fiber y) ≤ topologicalKrullDim
      ((AlgebraicGeometry.blowUpToBase (Stacks.LocalCohomology.specIdealSheaf S.A S.I)).fiber
        (S.Yι y)) := by
  let ℐ := Stacks.LocalCohomology.specIdealSheaf S.A S.I
  let e := Stacks.Blowup.blowUpIso ℐ
  let ψ : situationExceptional S → AlgebraicGeometry.blowUp ℐ := fun p =>
    e.hom (situationExceptionalι S p)
  have hmem : ∀ p : (exceptionalToY S ⁻¹' {y}),
      ψ p.1 ∈ (AlgebraicGeometry.blowUpToBase ℐ ⁻¹' {S.Yι y}) := by
    rintro ⟨p, hp⟩
    change (e.hom ≫ AlgebraicGeometry.blowUpToBase ℐ) (situationExceptionalι S p) = S.Yι y
    rw [Stacks.Blowup.blowUpIso_hom_comp, ← Scheme.Hom.comp_apply, ← exceptionalToY_Yι,
      Scheme.Hom.comp_apply, Set.mem_singleton_iff.mp hp]
  let φ := Set.codRestrict (fun p : (exceptionalToY S ⁻¹' {y}) => ψ p.1) _ hmem
  have hφ : Topology.IsInducing φ :=
    ((e.hom.isOpenEmbedding.isInducing.comp
      (situationExceptionalι S).isClosedEmbedding.isInducing).comp
        Topology.IsInducing.subtypeVal).codRestrict hmem
  exact (((AlgebraicGeometry.blowUpToBase ℐ).fiberHomeo (S.Yι y)).symm.isInducing.comp
    (hφ.comp ((exceptionalToY S).fiberHomeo y).isInducing)).topologicalKrullDim_le

/-- An immediate specialization between points in the image of an embedding is an immediate
specialization of the points themselves. -/
theorem IsImmediateSpecialization.of_isEmbedding {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : Topology.IsEmbedding f) {x y : X}
    (h : IsImmediateSpecialization (f x) (f y)) : IsImmediateSpecialization x y := by
  obtain ⟨hspec, hne, hmid⟩ := h
  exact ⟨hf.isInducing.specializes_iff.mp hspec, fun he => hne (congrArg f he),
    fun z hxz hzy =>
      (hmid (f z) (hxz.map hf.continuous) (hzy.map hf.continuous)).imp
        (fun h => hf.injective h) fun h => hf.injective h⟩

/-- The subset `{y ∈ U' ∩ Y' | δ^{Y'}_{Z'}(y) ≤ k}` of `U'`. -/
def blowupT (k : ℕ∞) : Set (situationBlowUpU S).toScheme :=
  {x | ∃ e : situationExceptional S, situationExceptionalι S e = (situationBlowUpU S).ι x ∧
    exceptionalDistance S e ≤ k}

/-- The sublevel sets `blowupT S k` are monotone in `k`. -/
theorem blowupT_mono {k l : ℕ∞} (hkl : k ≤ l) : blowupT S k ⊆ blowupT S l :=
  fun _ ⟨e, he, hk⟩ => ⟨e, he, hk.trans hkl⟩

/-- The ideal `I𝒪_{U'}` on `U'`. -/
abbrev blowupIdealU : (situationBlowUpU S).toScheme.IdealSheafData :=
  (situationExceptionalIdeal S).comap (situationBlowUpU S).ι

/-- A point of `U'` lies in the support of `I𝒪_{U'}` exactly when it lies in the image of `Y'`. -/
theorem mem_support_blowupIdealU_iff (x : (situationBlowUpU S).toScheme) :
    x ∈ ((blowupIdealU S).support : Set _) ↔
      ∃ e : situationExceptional S, situationExceptionalι S e = (situationBlowUpU S).ι x := by
  rw [SetLike.mem_coe, mem_support_comap_iff]
  change (situationBlowUpU S).ι x ∈ ((situationExceptionalIdeal S).support : Set _) ↔ _
  rw [← Scheme.IdealSheafData.range_subschemeι]
  rfl

/-- The set `blowupT S k` is contained in the support of `I𝒪_{U'}`. -/
theorem blowupT_subset_support (k : ℕ∞) : blowupT S k ⊆ ((blowupIdealU S).support : Set _) :=
  fun x ⟨e, he, _⟩ => (mem_support_blowupIdealU_iff S x).2 ⟨e, he⟩

/-- The set `blowupT S k` is stable under specialization in `U'`. -/
theorem stableUnderSpecialization_blowupT (k : ℕ∞) : StableUnderSpecialization (blowupT S k) := by
  rintro x x' hxx' ⟨e, he, hk⟩
  obtain ⟨e', he'⟩ := (mem_support_blowupIdealU_iff S x').1
    (hxx'.mem_closed (blowupIdealU S).support.isClosed
      ((mem_support_blowupIdealU_iff S x).2 ⟨e, he⟩))
  have hee' : e ⤳ e' := by
    rw [← (situationExceptionalι S).isClosedEmbedding.isInducing.specializes_iff, he, he']
    exact hxx'.map (situationBlowUpU S).ι.continuous
  exact ⟨e', he', distanceFunction_sublevel_stableUnderSpecialization _ _ k hee' hk⟩

/-- **Condition (e) of [Stacks, Tag 0EJF] for `T' = {δ ≤ 1} ⊆ T = {δ ≤ 2}`**, from
[Stacks, Tag 0EIY] part (7) on the catenary scheme `Y'`. -/
theorem mem_blowupT_two_of_isImmediateSpecialization
    (hcat : IrreducibleClosedsCodim.IsCatenarySpace (situationExceptional S))
    (x x' : (situationBlowUpU S).toScheme) (hx : x ∈ ((blowupIdealU S).support : Set _))
    (hxx' : IsImmediateSpecialization x x') (hx' : x' ∈ blowupT S 1) : x ∈ blowupT S 2 := by
  obtain ⟨e', he', hk⟩ := hx'
  obtain ⟨e, he⟩ := (mem_support_blowupIdealU_iff S x).1 hx
  have him : IsImmediateSpecialization e e' := by
    refine IsImmediateSpecialization.of_isEmbedding
      (situationExceptionalι S).isClosedEmbedding.isEmbedding ?_
    rw [he, he']
    exact hxx'.map_of_isOpenEmbedding (situationBlowUpU S).ι.isOpenEmbedding
  refine ⟨e, he, ?_⟩
  calc exceptionalDistance S e ≤ exceptionalDistance S e' + 1 :=
        distanceFunction_le_add_one_of_isImmediateSpecialization _ _ hcat him
    _ ≤ 1 + 1 := by gcongr
    _ = 2 := by norm_num

end Stacks.Algebraization

end
