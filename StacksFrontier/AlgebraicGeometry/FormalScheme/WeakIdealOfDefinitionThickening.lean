module

public import StacksFrontier.AlgebraicGeometry.FormalScheme.WeakIdealOfDefinitionPoints
public import StacksFrontier.AlgebraicGeometry.Crystalline.SpecSchemeThickening
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Stability

/-!
# The scheme `(𝔛, 𝒪_𝔛/ℐ)` is a thickening of `h_𝔛`

Let `𝔛` be a formal scheme in the sense of McQuillan and `ℐ` a weak ideal of definition of `𝔛` cut
out by its sections over the weak affine formal opens. The morphism `h_{(𝔛, 𝒪_𝔛/ℐ)} → h_𝔛` of
`AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf.quotientMorphism` is a *thickening*
in the sense of Stacks 0AIV: it is representable, and its base change along any point `T → 𝔛` of a
scheme is a thickening of schemes `W → T`. The scheme `W` represents the morphisms `T' → T` whose
composite with the point kills `ℐ`; over an affine open `V ⊆ T` mapping into a weak affine formal
open `𝔘 ≅ Spfw A`, the point factors through some `Spec (A/L)`, and `W ∩ V` is the base change of
the thickening `Spec (A/ℐ(𝔘)) → Spec (A/L)`.

## Main results

* `LocallyTopologicallyRingedSpace.IdealSheaf.isThickening_presheaf_quotientMorphism`:
  `h_{(𝔛, 𝒪_𝔛/ℐ)} → h_𝔛` is a thickening.

## References

* [Stacks Project, Tag 0AIV](https://stacks.math.columbia.edu/tag/0AIV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf

/-- Composition of the images of two morphisms of schemes with a third morphism. -/
theorem schemeToLTRS_map_comp_assoc {T₁ T₂ T₃ : Scheme.{u}} {Y : LTRS.{u}} (a : T₁ ⟶ T₂)
    (b : T₂ ⟶ T₃) (c : schemeToLTRSObj T₃ ⟶ Y) :
    schemeToLTRS.map (a ≫ b) ≫ c = schemeToLTRS.map a ≫ (schemeToLTRS.map b ≫ c) :=
  (congrArg (· ≫ c) (schemeToLTRS.map_comp a b)).trans (Category.assoc _ _ _)

/-- The quotient point of a chart is a monomorphism on points over schemes. -/
theorem weakChartPoint_cancel {X : LTRS.{u}} {U : Opens X} (A : Type u) [CommRing A]
    [TopologicalSpace A] [IsTopologicalRing A] [IsLinearTopology A A]
    (hA : TopologicalRing.IsWeaklyAdmissible A) (χ : X.restrict U ≅ spfwLTRS A hA.1)
    (J : WeakIdealsOfDefinition A) {T : Scheme.{u}} {b b' : T ⟶ Spec (spfQuotientOn A J)}
    (h : schemeToLTRS.map b ≫ weakChartPoint A hA χ J =
      schemeToLTRS.map b' ≫ weakChartPoint A hA χ J) : b = b' :=
  spfwQuotientPoint_cancel A hA J (weakChartEmbedding_cancel A hA χ
    ((Category.assoc _ _ _).trans (h.trans (Category.assoc _ _ _).symm)))

section Pullback

variable {𝔛 : McQuillanFormalScheme.{u}} (I : IdealSheaf 𝔛.obj)
  (hI : I.IsWeakIdealOfDefinitionOn (IsWeakAffineFormalOpen 𝔛.obj))
  (hC : I.IsCutOutOn (IsWeakAffineFormalOpen 𝔛.obj))
  {T : Scheme.{u}} (φ : schemeToLTRSObj T ⟶ 𝔛.obj)

/-- The morphisms `T' → T` whose composite with a point `φ : T → 𝔛` kills `ℐ`: the base change of
`h_{(𝔛, 𝒪_𝔛/ℐ)} → h_𝔛` along `φ`. -/
def pullbackPoints : Subfunctor (yoneda.obj T) where
  obj T' := {k | I.Kills (schemeToLTRS.map k ≫ φ)}
  map {T₁ T₂} g k hk := by
    change I.Kills (schemeToLTRS.map (g.unop ≫ k) ≫ φ)
    rw [schemeToLTRS_map_comp_assoc]
    exact hk.comp _

/-- The base change of `h_{(𝔛, 𝒪_𝔛/ℐ)}` along a point is a Zariski sheaf. -/
theorem isSheaf_pullbackPoints :
    Presieve.IsSheaf Scheme.zariskiTopology (pullbackPoints I φ).toFunctor := by
  rw [Subfunctor.isSheaf_iff _
    (GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable (yoneda.obj T))]
  intro T' k hk
  obtain ⟨𝒰, h𝒰⟩ := Scheme.exists_cover_of_mem_grothendieckTopology hk
  have hopen : ∀ j, IsOpenImmersion (𝒰.f j) := fun j => 𝒰.map_prop j
  let W : 𝒰.I₀ → T'.unop.Opens := fun j => (𝒰.f j).opensRange
  refine kills_of_openCover I (schemeToLTRS.map k ≫ φ) W
    (iSup_eq_top_of_forall_exists_mem W fun x => by
      obtain ⟨j, y, hy⟩ := 𝒰.exists_eq x
      exact ⟨j, ⟨y, hy⟩⟩) fun j => ?_
  have hmem : (pullbackPoints I φ).sieveOfSection k (W j).ι := by
    have hj : (pullbackPoints I φ).sieveOfSection k (𝒰.f j) := h𝒰 _ _ (Presieve.ofArrows.mk j)
    have := Sieve.downward_closed _ hj
      (IsOpenImmersion.isoOfRangeEq (W j).ι (𝒰.f j) (W j).range_ι).hom
    rwa [IsOpenImmersion.isoOfRangeEq_hom_fac (W j).ι (𝒰.f j) (W j).range_ι] at this
  have h' : I.Kills (schemeToLTRS.map ((W j).ι ≫ k) ≫ φ) := hmem
  rwa [schemeToLTRS_map_comp_assoc] at h'

/-- The sheaf of the base change of `h_{(𝔛, 𝒪_𝔛/ℐ)}` along a point. -/
noncomputable def pullbackPointsSheaf : Sheaf Scheme.zariskiTopology.{u} (Type u) :=
  ⟨(pullbackPoints I φ).toFunctor, (isSheaf_iff_isSheaf_of_type _ _).mpr
    (isSheaf_pullbackPoints I φ)⟩

/-- An affine open of `T` mapped by the point `φ` into a weak affine formal open of `𝔛`. -/
structure PullbackChart where
  /-- The affine open of `T`. -/
  V : T.Opens
  isAffineOpen : IsAffineOpen V
  /-- The weak affine formal open of `𝔛`. -/
  U : Opens 𝔛.obj
  isWeakAffineFormalOpen : IsWeakAffineFormalOpen 𝔛.obj U
  maps_to : ∀ x ∈ V, φ.toHom.base x ∈ U

variable {φ}

namespace PullbackChart

variable (p : PullbackChart φ)

/-- The point `φ` restricted to the affine open of a pullback chart. -/
noncomputable abbrev point : schemeToLTRSObj p.V.toScheme ⟶ 𝔛.obj :=
  schemeToLTRS.map p.V.ι ≫ φ

/-- The restricted point lands in the weak affine formal open of the chart. -/
theorem range_point_subset : Set.range p.point.toHom.base ⊆ (p.U : Set 𝔛.obj) := by
  rintro _ ⟨y, rfl⟩
  exact p.maps_to y.1 y.2

/-- The affine open of a pullback chart is quasi-compact. -/
instance compactSpace : CompactSpace p.V.toScheme :=
  isCompact_iff_compactSpace.mp p.isAffineOpen.isCompact

/-- A weak ideal of definition of the chart ring killed by the restricted point, chosen. -/
noncomputable def stage₀ : WeakIdealsOfDefinition p.isWeakAffineFormalOpen.chart.ring.α :=
  (exists_weakIdeal_kill_weakChartSections _ p.isWeakAffineFormalOpen.chart.admissible
    p.isWeakAffineFormalOpen.chart.iso p.point p.range_point_subset).choose

/-- The stage through which the restricted point factors: the meet of `stage₀` with the chart
ideal of `ℐ`. -/
noncomputable def stage : WeakIdealsOfDefinition p.isWeakAffineFormalOpen.chart.ring.α :=
  spfIndexMeet _ p.stage₀ (I.chartIdeal hI p.isWeakAffineFormalOpen)

/-- The stage is contained in the chart ideal of `ℐ`. -/
theorem stage_le : (p.stage I hI).1 ≤ (I.chartIdeal hI p.isWeakAffineFormalOpen).1 :=
  inf_le_right

/-- The restricted point kills the stage: it sends every element of the stage, as a section over
`𝔘` through the chart, to zero. -/
theorem kills_stage : ∀ a ∈ (p.stage I hI).1,
    (p.point.toHom.c.app (op p.U)).1 ((weakChartSections _ p.isWeakAffineFormalOpen.chart.admissible
      p.isWeakAffineFormalOpen.chart.iso).1 a) = 0 := fun a ha =>
  (exists_weakIdeal_kill_weakChartSections _ p.isWeakAffineFormalOpen.chart.admissible
    p.isWeakAffineFormalOpen.chart.iso p.point p.range_point_subset).choose_spec a ha.1

/-- The factorisation `V → Spec (A/L)` of the restricted point through its stage. -/
noncomputable def factor : p.V.toScheme ⟶ Spec (spfQuotientOn _ (p.stage I hI)) :=
  (existsUnique_weakChartPoint_factor _ p.isWeakAffineFormalOpen.chart.admissible
    p.isWeakAffineFormalOpen.chart.iso (p.stage I hI) p.point p.range_point_subset
    (p.kills_stage I hI)).choose

/-- The factorisation `V → Spec (A/L)` followed by the quotient point of the stage is the
restricted point. -/
theorem factor_comp : schemeToLTRS.map (p.factor I hI) ≫ weakChartPoint _
    p.isWeakAffineFormalOpen.chart.admissible p.isWeakAffineFormalOpen.chart.iso (p.stage I hI) =
      p.point :=
  (existsUnique_weakChartPoint_factor _ p.isWeakAffineFormalOpen.chart.admissible
    p.isWeakAffineFormalOpen.chart.iso (p.stage I hI) p.point p.range_point_subset
    (p.kills_stage I hI)).choose_spec.1

/-- The thickening `Spec (A/ℐ(𝔘)) → Spec (A/L)` of the stage. -/
noncomputable abbrev transition : I.chartScheme hI p.isWeakAffineFormalOpen ⟶
    Spec (spfQuotientOn _ (p.stage I hI)) :=
  Spec.map (CommRingCat.ofHom (Ideal.Quotient.factor (p.stage_le I hI)))

/-- The thickening `Spec (A/ℐ(𝔘)) → Spec (A/L)` followed by the quotient point of the stage is the
quotient point of `ℐ` on the chart. -/
theorem transition_comp :
    schemeToLTRS.map (p.transition I hI) ≫ weakChartPoint _
      p.isWeakAffineFormalOpen.chart.admissible p.isWeakAffineFormalOpen.chart.iso (p.stage I hI) =
        I.chartPoint hI p.isWeakAffineFormalOpen :=
  schemeToLTRS_map_comp_weakChartPoint _ _ _ (p.stage_le I hI)

/-- The local piece `V ×_{Spec (A/L)} Spec (A/ℐ(𝔘))` of the base change. -/
noncomputable abbrev piece : Scheme.{u} := pullback (p.factor I hI) (p.transition I hI)

/-- The local piece maps to `T` by a morphism whose composite with `φ` factors through the quotient
point of the chart. -/
theorem piece_comp :
    schemeToLTRS.map (pullback.fst (p.factor I hI) (p.transition I hI) ≫ p.V.ι) ≫ φ =
      schemeToLTRS.map (pullback.snd (p.factor I hI) (p.transition I hI)) ≫
        I.chartPoint hI p.isWeakAffineFormalOpen := by
  refine (schemeToLTRS_map_comp_assoc _ _ _).trans ?_
  refine (congrArg (schemeToLTRS.map (pullback.fst _ _) ≫ ·) (p.factor_comp I hI).symm).trans ?_
  refine (schemeToLTRS_map_comp_assoc _ _ _).symm.trans ?_
  refine (congrArg (fun m => schemeToLTRS.map m ≫ _) pullback.condition).trans ?_
  refine (schemeToLTRS_map_comp_assoc _ _ _).trans ?_
  exact congrArg (schemeToLTRS.map (pullback.snd _ _) ≫ ·) (p.transition_comp I hI)

/-- The thickening `Spec (A/ℐ(𝔘)) → Spec (A/L)`: `ℐ(𝔘)` consists of topologically nilpotent
elements and `L` is open, so the kernel `ℐ(𝔘)/L` is nil. -/
theorem isThickening_transition : Stacks.Thickenings.IsThickening (p.transition I hI) := by
  refine Stacks.Thickenings.specMap_isThickening_of_nilKernel _
    (Ideal.Quotient.factor_surjective (p.stage_le I hI)) fun x hx => ?_
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  have ha : a ∈ (I.chartIdeal hI p.isWeakAffineFormalOpen).1 :=
    Ideal.Quotient.eq_zero_iff_mem.mp (by simpa using hx)
  obtain ⟨n, hn⟩ := ((I.chartIdeal hI p.isWeakAffineFormalOpen).2.2 a ha).exists_pow_mem_of_mem_nhds
    ((p.stage I hI).2.1.mem_nhds (p.stage I hI).1.zero_mem)
  refine ⟨n, ?_⟩
  rw [← map_pow]
  exact Ideal.Quotient.eq_zero_iff_mem.mpr hn

/-- The first projection `V ×_{Spec (A/L)} Spec (A/ℐ(𝔘)) → V` of the local piece is a
thickening, as a base change of the thickening `Spec (A/ℐ(𝔘)) → Spec (A/L)`. -/
theorem isThickening_piece_fst :
    Stacks.Thickenings.IsThickening (pullback.fst (p.factor I hI) (p.transition I hI)) :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Stacks.Thickenings.IsThickening)
    (IsPullback.of_hasPullback _ _).flip (p.isThickening_transition I hI)

/-- The point of the base change given by a local piece. -/
noncomputable def pieceElement : (pullbackPoints I φ).toFunctor.obj (op (p.piece I hI)) :=
  ⟨pullback.fst (p.factor I hI) (p.transition I hI) ≫ p.V.ι, by
    change I.Kills (schemeToLTRS.map (pullback.fst (p.factor I hI) (p.transition I hI) ≫ p.V.ι) ≫ φ)
    rw [p.piece_comp I hI]
    exact (kills_chartPoint hC p.isWeakAffineFormalOpen).comp _⟩

/-- The morphism `h_{piece} → h_ℐ ×_{h_𝔛} h_T` of a local piece. -/
noncomputable def pieceMap : yoneda.obj (p.piece I hI) ⟶ (pullbackPoints I φ).toFunctor :=
  yonedaEquiv.symm (p.pieceElement I hI hC)

/-- The morphism `h_{piece} → h_ℐ ×_{h_𝔛} h_T` of a local piece sends `x` to its composite with
the projection of the local piece to `T`. -/
theorem pieceMap_app_val {T' : Scheme.{u}} (x : T' ⟶ p.piece I hI) :
    ((p.pieceMap I hI hC).app (op T') x).1 =
      x ≫ pullback.fst (p.factor I hI) (p.transition I hI) ≫ p.V.ι :=
  rfl

/-- The inclusion of `k⁻¹(V)` followed by `k : T' → T` lands in `V`. -/
theorem range_preimage_ι_comp_subset {T' : Scheme.{u}} (k : T' ⟶ T) :
    Set.range ((k ⁻¹ᵁ p.V).ι ≫ k) ⊆ Set.range p.V.ι := by
  rintro _ ⟨y, rfl⟩
  rw [Scheme.Opens.range_ι]
  exact y.2

/-- The restriction `k⁻¹(V) → V` of a morphism `k : T' → T` to the preimage of the affine open of a
chart. -/
noncomputable def restrictV {T' : Scheme.{u}} (k : T' ⟶ T) : (k ⁻¹ᵁ p.V).toScheme ⟶ p.V.toScheme :=
  IsOpenImmersion.lift p.V.ι ((k ⁻¹ᵁ p.V).ι ≫ k) (p.range_preimage_ι_comp_subset k)

/-- The restriction `k⁻¹(V) → V` followed by `V ↪ T` is the inclusion of `k⁻¹(V)` followed by
`k`. -/
theorem restrictV_ι {T' : Scheme.{u}} (k : T' ⟶ T) :
    p.restrictV k ≫ p.V.ι = (k ⁻¹ᵁ p.V).ι ≫ k :=
  IsOpenImmersion.lift_fac _ _ _

/-- The point `k⁻¹(V) → T → 𝔛` lands in the weak affine formal open of the chart. -/
theorem range_restrictPoint_subset {T' : Scheme.{u}} (k : T' ⟶ T) :
    Set.range (schemeToLTRS.map ((k ⁻¹ᵁ p.V).ι ≫ k) ≫ φ).toHom.base ⊆ (p.U : Set 𝔛.obj) := by
  rintro _ ⟨y, rfl⟩
  exact p.maps_to _ y.2

/-- If `k` followed by `φ` kills `ℐ`, then the point `k⁻¹(V) → T → 𝔛` kills the sections of `ℐ`
over the weak affine formal open of the chart. -/
theorem restrictPoint_kills {T' : Scheme.{u}} {k : T' ⟶ T} (hk : I.Kills (schemeToLTRS.map k ≫ φ)) :
    ∀ t ∈ I.ideal p.U,
      ((schemeToLTRS.map ((k ⁻¹ᵁ p.V).ι ≫ k) ≫ φ).toHom.c.app (op p.U)).1 t = 0 := fun t ht => by
  rw [schemeToLTRS_map_comp_assoc]
  exact mem_ker_iff.mp ((hk.comp (schemeToLTRS.map (k ⁻¹ᵁ p.V).ι)) p.U ht)

variable {I hI} in
/-- The factorisation `k⁻¹(V) → Spec (A/ℐ(𝔘))` of a morphism `k` whose composite with `φ` kills
`ℐ`. -/
noncomputable def restrictQ {T' : Scheme.{u}} {k : T' ⟶ T} (hk : I.Kills (schemeToLTRS.map k ≫ φ)) :
    (k ⁻¹ᵁ p.V).toScheme ⟶ I.chartScheme hI p.isWeakAffineFormalOpen :=
  (I.existsUnique_chartPoint_factor hI p.isWeakAffineFormalOpen _ (p.range_restrictPoint_subset k)
    (p.restrictPoint_kills I hk)).choose

/-- The factorisation `k⁻¹(V) → Spec (A/ℐ(𝔘))` followed by the quotient point of `ℐ` on the chart
is the point `k⁻¹(V) → T → 𝔛`. -/
theorem restrictQ_comp {T' : Scheme.{u}} {k : T' ⟶ T} (hk : I.Kills (schemeToLTRS.map k ≫ φ)) :
    schemeToLTRS.map (p.restrictQ (hI := hI) hk) ≫ I.chartPoint hI p.isWeakAffineFormalOpen =
      schemeToLTRS.map ((k ⁻¹ᵁ p.V).ι ≫ k) ≫ φ :=
  (I.existsUnique_chartPoint_factor hI p.isWeakAffineFormalOpen _ (p.range_restrictPoint_subset k)
    (p.restrictPoint_kills I hk)).choose_spec.1

/-- The restriction `k⁻¹(V) → V` followed by `V → Spec (A/L)` equals the factorisation
`k⁻¹(V) → Spec (A/ℐ(𝔘))` followed by the thickening `Spec (A/ℐ(𝔘)) → Spec (A/L)`. -/
theorem restrictV_factor {T' : Scheme.{u}} {k : T' ⟶ T} (hk : I.Kills (schemeToLTRS.map k ≫ φ)) :
    p.restrictV k ≫ p.factor I hI = p.restrictQ (hI := hI) hk ≫ p.transition I hI := by
  refine weakChartPoint_cancel _ p.isWeakAffineFormalOpen.chart.admissible
    p.isWeakAffineFormalOpen.chart.iso (p.stage I hI) ?_
  refine (schemeToLTRS_map_comp_assoc _ _ _).trans ?_
  refine (congrArg (schemeToLTRS.map (p.restrictV k) ≫ ·) (p.factor_comp I hI)).trans ?_
  refine (schemeToLTRS_map_comp_assoc _ _ _).symm.trans ?_
  refine (congrArg (fun z => schemeToLTRS.map z ≫ φ) (p.restrictV_ι k)).trans ?_
  refine (p.restrictQ_comp I hI hk).symm.trans ?_
  refine (congrArg (schemeToLTRS.map (p.restrictQ hk) ≫ ·) (p.transition_comp I hI)).symm.trans ?_
  exact (schemeToLTRS_map_comp_assoc _ _ _).symm

variable {I hI} in
/-- The lift `k⁻¹(V) → V ×_{Spec (A/L)} Spec (A/ℐ(𝔘))` of a morphism `k : T' → T` whose composite
with `φ` kills `ℐ`. -/
noncomputable def pieceLift {T' : Scheme.{u}} {k : T' ⟶ T} (hk : I.Kills (schemeToLTRS.map k ≫ φ)) :
    (k ⁻¹ᵁ p.V).toScheme ⟶ p.piece I hI :=
  pullback.lift (p.restrictV k) (p.restrictQ hk) (p.restrictV_factor I hI hk)

/-- The lift `k⁻¹(V) → V ×_{Spec (A/L)} Spec (A/ℐ(𝔘))` followed by the first projection is the
restriction `k⁻¹(V) → V`. -/
theorem pieceLift_fst {T' : Scheme.{u}} {k : T' ⟶ T} (hk : I.Kills (schemeToLTRS.map k ≫ φ)) :
    p.pieceLift (I := I) (hI := hI) hk ≫ pullback.fst _ _ = p.restrictV k :=
  pullback.lift_fst _ _ _

/-- The lift `k⁻¹(V) → V ×_{Spec (A/L)} Spec (A/ℐ(𝔘))` followed by the second projection is the
factorisation `k⁻¹(V) → Spec (A/ℐ(𝔘))`. -/
theorem pieceLift_snd {T' : Scheme.{u}} {k : T' ⟶ T} (hk : I.Kills (schemeToLTRS.map k ≫ φ)) :
    p.pieceLift (I := I) (hI := hI) hk ≫ pullback.snd _ _ = p.restrictQ hk :=
  pullback.lift_snd _ _ _

/-- The lift `k⁻¹(V) → V ×_{Spec (A/L)} Spec (A/ℐ(𝔘))` followed by the projection to `T` is the
inclusion of `k⁻¹(V)` followed by `k`. -/
theorem pieceLift_fst_ι {T' : Scheme.{u}} {k : T' ⟶ T} (hk : I.Kills (schemeToLTRS.map k ≫ φ)) :
    p.pieceLift (I := I) (hI := hI) hk ≫ pullback.fst _ _ ≫ p.V.ι = (k ⁻¹ᵁ p.V).ι ≫ k := by
  rw [← Category.assoc, pieceLift_fst, restrictV_ι]

/-- Two morphisms into a local piece agree as soon as their composites with `T` agree: the first
projection is determined after `V ↪ T`, and the second by the quotient point of the chart. -/
theorem piece_hom_ext {T' : Scheme.{u}} {x y : T' ⟶ p.piece I hI}
    (h : x ≫ pullback.fst _ _ ≫ p.V.ι = y ≫ pullback.fst _ _ ≫ p.V.ι) : x = y := by
  have hfst : x ≫ pullback.fst (p.factor I hI) (p.transition I hI) =
      y ≫ pullback.fst (p.factor I hI) (p.transition I hI) :=
    (cancel_mono p.V.ι).mp (by simpa only [Category.assoc] using h)
  refine pullback.hom_ext hfst (weakChartPoint_cancel _ p.isWeakAffineFormalOpen.chart.admissible
    p.isWeakAffineFormalOpen.chart.iso (I.chartIdeal hI p.isWeakAffineFormalOpen) ?_)
  change schemeToLTRS.map _ ≫ I.chartPoint hI p.isWeakAffineFormalOpen =
    schemeToLTRS.map _ ≫ I.chartPoint hI p.isWeakAffineFormalOpen
  refine (schemeToLTRS_map_comp_assoc _ _ _).trans ?_
  refine (congrArg (schemeToLTRS.map x ≫ ·) (p.piece_comp I hI).symm).trans ?_
  refine (schemeToLTRS_map_comp_assoc _ _ _).symm.trans ?_
  refine (congrArg (fun z => schemeToLTRS.map z ≫ φ) h).trans ?_
  refine (schemeToLTRS_map_comp_assoc _ _ _).trans ?_
  refine (congrArg (schemeToLTRS.map y ≫ ·) (p.piece_comp I hI)).trans ?_
  exact (schemeToLTRS_map_comp_assoc _ _ _).symm

/-- A morphism `h_{T'} → h_ℐ ×_{h_𝔛} h_T` acts by precomposition on its own point. -/
theorem app_val_eq {T' T'' : Scheme.{u}} (g : yoneda.obj T' ⟶ (pullbackPoints I φ).toFunctor)
    (y : T'' ⟶ T') : (g.app (op T'') y).1 = y ≫ (yonedaEquiv g).1 := by
  rw [← map_yonedaEquiv]
  rfl

/-- **The local pieces of the base change are relatively representable open immersions.** The base
change of a local piece along a morphism `k : T' → T` killing `ℐ` is the open subscheme
`k⁻¹(V) ⊆ T'`. -/
theorem isOpenImmersion_presheaf_pieceMap : IsOpenImmersion.presheaf (p.pieceMap I hI hC) := by
  refine MorphismProperty.relative.of_exists fun T' g => ?_
  set k := (yonedaEquiv g).1
  have hk : I.Kills (schemeToLTRS.map k ≫ φ) := (yonedaEquiv g).2
  refine ⟨_, yoneda.map (p.pieceLift (I := I) (hI := hI) hk), (k ⁻¹ᵁ p.V).ι, ?_, inferInstance⟩
  refine IsPullback.of_forall_isPullback_app fun T'' => ?_
  induction T'' using Opposite.rec with
  | op T'' =>
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext x
    refine Subtype.ext ?_
    change ((p.pieceMap I hI hC).app (op T'') (x ≫ p.pieceLift hk)).1 =
      (g.app (op T'') (x ≫ (k ⁻¹ᵁ p.V).ι)).1
    rw [pieceMap_app_val, app_val_eq]
    change x ≫ p.pieceLift hk ≫ pullback.fst _ _ ≫ p.V.ι = x ≫ (k ⁻¹ᵁ p.V).ι ≫ k
    rw [pieceLift_fst_ι]
  · rintro (x₁ : T'' ⟶ _) (x₂ : T'' ⟶ _) ⟨-, h₂⟩
    exact (cancel_mono (k ⁻¹ᵁ p.V).ι).mp h₂
  · intro (x : T'' ⟶ p.piece I hI) (y : T'' ⟶ T') hxy
    have hxy' : x ≫ pullback.fst _ _ ≫ p.V.ι = y ≫ k := by
      have := congrArg Subtype.val hxy
      rwa [pieceMap_app_val, app_val_eq] at this
    have hy : Set.range y ⊆ Set.range (k ⁻¹ᵁ p.V).ι := by
      rintro _ ⟨z, rfl⟩
      rw [Scheme.Opens.range_ι]
      change (y ≫ k) z ∈ p.V
      rw [← hxy']
      exact ((x ≫ pullback.fst (p.factor I hI) (p.transition I hI)) z).2
    refine ⟨IsOpenImmersion.lift _ y hy, ?_, IsOpenImmersion.lift_fac _ _ _⟩
    refine p.piece_hom_ext I hI ?_
    change (IsOpenImmersion.lift _ y hy ≫ p.pieceLift hk) ≫ pullback.fst _ _ ≫ p.V.ι = _
    rw [Category.assoc, pieceLift_fst_ι, ← Category.assoc, IsOpenImmersion.lift_fac, hxy']

end PullbackChart

/-- The local pieces of the base change, as a family of morphisms into the sheaf. -/
noncomputable abbrev pieceFamily (p : PullbackChart φ) :
    yoneda.obj (p.piece I hI) ⟶ (pullbackPointsSheaf I φ).1 :=
  p.pieceMap I hI hC

namespace PullbackChart

/-- Every point of `T` lies in the affine open of some pullback chart. -/
private theorem exists_pullbackChart_mem (h𝔛 : IsMcQuillanFormalScheme 𝔛.obj) :
    ∃ c : T → PullbackChart φ, ∀ q, q ∈ (c q).V := by
  choose U hxU hU using (isMcQuillanFormalScheme_iff_forall_isWeakAffineFormalOpen _).mp h𝔛
  have hV : ∀ q : T, ∃ V : T.Opens, IsAffineOpen V ∧ q ∈ V ∧ ∀ x ∈ V, φ.toHom.base x ∈
      U (φ.toHom.base q) := fun q => by
    obtain ⟨_, ⟨V, hV, rfl⟩, hqV, hVU⟩ := T.isBasis_affineOpens.exists_subset_of_mem_open
      (show q ∈ (φ.toHom.base ⁻¹' (U (φ.toHom.base q) : Set 𝔛.obj) : Set T) from hxU _)
      (show IsOpen (φ.toHom.base ⁻¹' (U (φ.toHom.base q) : Set 𝔛.obj) : Set T) from
        ((Opens.map φ.toHom.base).obj (U (φ.toHom.base q))).isOpen)
    exact ⟨V, hV, hqV, fun x hx => hVU hx⟩
  choose V hVa hqV hVU using hV
  let c : T → PullbackChart φ := fun q =>
    ⟨V q, hVa q, U (φ.toHom.base q), hU _, hVU q⟩
  exact ⟨c, hqV⟩

/-- **The local pieces of the base change are jointly surjective, Zariski locally.** -/
theorem isLocallySurjective_sigmaDesc_pieceMap (h𝔛 : IsMcQuillanFormalScheme 𝔛.obj) :
    Presheaf.IsLocallySurjective Scheme.zariskiTopology
      (Sigma.desc (pieceFamily I hI hC (φ := φ))) := by
  refine ⟨fun {T'} k => ?_⟩
  obtain ⟨c, hc⟩ := exists_pullbackChart_mem (φ := φ) h𝔛
  let k' : T' ⟶ T := k.1
  have hk : I.Kills (schemeToLTRS.map k' ≫ φ) := k.2
  rw [Scheme.mem_grothendieckTopology_iff]
  refine ⟨Scheme.Cover.mkOfCovers T' (fun q => (k' ⁻¹ᵁ (c (k' q)).V).toScheme)
    (fun q => (k' ⁻¹ᵁ (c (k' q)).V).ι) (fun q => ⟨q, ⟨q, hc _⟩, rfl⟩), ?_⟩
  rintro _ _ ⟨q⟩
  refine ⟨(Sigma.ι (fun p : PullbackChart φ => yoneda.obj (p.piece I hI)) (c (k' q))).app _
    ((c (k' q)).pieceLift (I := I) (hI := hI) hk), ?_⟩
  have h := congrArg (fun η => η.app (op (k' ⁻¹ᵁ (c (k' q)).V).toScheme)
      ((c (k' q)).pieceLift (I := I) (hI := hI) hk))
    (Sigma.ι_desc (pieceFamily I hI hC (φ := φ)) (c (k' q)))
  simp only [NatTrans.comp_app, types_comp_apply] at h
  exact h.trans (Subtype.ext ((c (k' q)).pieceLift_fst_ι I hI hk))

end PullbackChart

/-! ### The base change as a scheme -/

/-- The base change of `h_{(𝔛, 𝒪_𝔛/ℐ)} → h_𝔛` along a point `φ : T → 𝔛`, as a scheme glued from the
local pieces. -/
noncomputable def pullbackScheme : Scheme.{u} :=
  (Scheme.LocalRepresentability.glueData (F := pullbackPointsSheaf I φ)
    (f := pieceFamily I hI hC (φ := φ))
    (fun p : PullbackChart φ => p.isOpenImmersion_presheaf_pieceMap I hI hC)).glued

/-- The base change scheme represents the morphisms `T' → T` whose composite with `φ` kills `ℐ`. -/
noncomputable def pullbackSchemeRepresentableBy (h𝔛 : IsMcQuillanFormalScheme 𝔛.obj) :
    (pullbackPoints I φ).toFunctor.RepresentableBy (pullbackScheme I hI hC (φ := φ)) :=
  haveI := PullbackChart.isLocallySurjective_sigmaDesc_pieceMap I hI hC (φ := φ) h𝔛
  Scheme.LocalRepresentability.representableBy (F := pullbackPointsSheaf I φ)
    (f := pieceFamily I hI hC (φ := φ))
    (fun p : PullbackChart φ => p.isOpenImmersion_presheaf_pieceMap I hI hC)

variable (h𝔛 : IsMcQuillanFormalScheme 𝔛.obj)

/-- The projection of the base change scheme to `T`. -/
noncomputable def pullbackProj : pullbackScheme I hI hC (φ := φ) ⟶ T :=
  ((pullbackSchemeRepresentableBy I hI hC h𝔛).homEquiv (𝟙 _)).1

/-- The morphism `T' → T` that the base change scheme assigns to `m : T' → W` is `m` followed by
the projection `W → T`. -/
theorem homEquiv_val {T' : Scheme.{u}} (m : T' ⟶ pullbackScheme I hI hC (φ := φ)) :
    ((pullbackSchemeRepresentableBy I hI hC h𝔛).homEquiv m).1 = m ≫ pullbackProj I hI hC h𝔛 := by
  rw [(pullbackSchemeRepresentableBy I hI hC h𝔛).homEquiv_eq]
  rfl

/-- The projection of the base change scheme to `T`, followed by `φ`, kills `ℐ`. -/
theorem kills_pullbackProj :
    I.Kills (schemeToLTRS.map (pullbackProj I hI hC h𝔛 (φ := φ)) ≫ φ) :=
  ((pullbackSchemeRepresentableBy I hI hC h𝔛).homEquiv (𝟙 _)).2

/-- **The universal property of the base change scheme.** -/
theorem existsUnique_pullbackProj_factor {T' : Scheme.{u}} (k : T' ⟶ T)
    (hk : I.Kills (schemeToLTRS.map k ≫ φ)) :
    ∃! m : T' ⟶ pullbackScheme I hI hC (φ := φ), m ≫ pullbackProj I hI hC h𝔛 = k := by
  set e := pullbackSchemeRepresentableBy I hI hC h𝔛 (φ := φ)
  let x : (pullbackPoints I φ).toFunctor.obj (op T') := ⟨k, hk⟩
  have hx := congrArg Subtype.val (e.homEquiv.apply_symm_apply x)
  exact ⟨e.homEquiv.symm x, (homEquiv_val I hI hC h𝔛 _).symm.trans hx,
    fun m hm => e.homEquiv.injective (Subtype.ext
      ((homEquiv_val I hI hC h𝔛 m).trans (hm.trans hx.symm)))⟩

/-- The projection of the base change scheme to `T` is a monomorphism. -/
instance mono_pullbackProj : Mono (pullbackProj I hI hC h𝔛 (φ := φ)) := by
  refine ⟨fun {T'} m₁ m₂ h => ?_⟩
  have hk : I.Kills (schemeToLTRS.map (m₂ ≫ pullbackProj I hI hC h𝔛) ≫ φ) := by
    rw [schemeToLTRS_map_comp_assoc]
    exact (kills_pullbackProj I hI hC h𝔛).comp _
  obtain ⟨m, -, huniq⟩ := existsUnique_pullbackProj_factor I hI hC h𝔛 _ hk
  exact (huniq m₁ h).trans (huniq m₂ rfl).symm

namespace PullbackChart

variable (p : PullbackChart φ)

/-- The morphism from a local piece to the base change scheme. -/
noncomputable def pieceToPullback : p.piece I hI ⟶ pullbackScheme I hI hC (φ := φ) :=
  (pullbackSchemeRepresentableBy I hI hC h𝔛).homEquiv.symm (p.pieceElement I hI hC)

/-- The morphism from a local piece to the base change scheme, followed by the projection to `T`,
is the projection of the local piece to `T`. -/
theorem pieceToPullback_proj :
    p.pieceToPullback I hI hC h𝔛 ≫ pullbackProj I hI hC h𝔛 (φ := φ) =
      pullback.fst (p.factor I hI) (p.transition I hI) ≫ p.V.ι := by
  rw [← homEquiv_val, pieceToPullback, Equiv.apply_symm_apply]
  rfl

/-- The morphism from a local piece to the base change scheme lands in the preimage of the affine
open of the chart. -/
theorem range_pieceToPullback_subset :
    Set.range (p.pieceToPullback I hI hC h𝔛) ⊆
      Set.range (pullbackProj I hI hC h𝔛 (φ := φ) ⁻¹ᵁ p.V).ι := by
  rintro _ ⟨z, rfl⟩
  rw [Scheme.Opens.range_ι]
  change (p.pieceToPullback I hI hC h𝔛 ≫ pullbackProj I hI hC h𝔛) z ∈ p.V
  rw [pieceToPullback_proj]
  exact ((pullback.fst (p.factor I hI) (p.transition I hI)) z).2

/-- **Over the affine open of a chart, the base change scheme is the local piece**: the lift of the
projection to the local piece is an isomorphism. -/
instance isIso_pieceLift :
    IsIso (p.pieceLift (I := I) (hI := hI) (kills_pullbackProj I hI hC h𝔛 (φ := φ))) := by
  set j := IsOpenImmersion.lift _ _ (p.range_pieceToPullback_subset I hI hC h𝔛)
  have hj : j ≫ (pullbackProj I hI hC h𝔛 ⁻¹ᵁ p.V).ι = p.pieceToPullback I hI hC h𝔛 :=
    IsOpenImmersion.lift_fac _ _ _
  have hj' : j ≫ (pullbackProj I hI hC h𝔛 ⁻¹ᵁ p.V).ι ≫ pullbackProj I hI hC h𝔛 =
      pullback.fst (p.factor I hI) (p.transition I hI) ≫ p.V.ι := by
    rw [← Category.assoc, hj, pieceToPullback_proj]
  refine ⟨j, ?_, ?_⟩
  · refine (cancel_mono (pullbackProj I hI hC h𝔛 ⁻¹ᵁ p.V).ι).mp ?_
    refine (cancel_mono (pullbackProj I hI hC h𝔛)).mp ?_
    simp only [Category.assoc, Category.id_comp]
    rw [hj', p.pieceLift_fst_ι I hI]
  · refine p.piece_hom_ext I hI ?_
    simp only [Category.assoc, Category.id_comp]
    rw [p.pieceLift_fst_ι I hI, hj']

/-- The restriction of the projection over the affine open of a chart is the base change of the
thickening `Spec (A/ℐ(𝔘)) → Spec (A/L)`. -/
theorem morphismRestrict_pullbackProj :
    pullbackProj I hI hC h𝔛 (φ := φ) ∣_ p.V =
      p.pieceLift (I := I) (hI := hI) (kills_pullbackProj I hI hC h𝔛 (φ := φ)) ≫
        pullback.fst (p.factor I hI) (p.transition I hI) := by
  refine (cancel_mono p.V.ι).mp ?_
  rw [morphismRestrict_ι, Category.assoc, p.pieceLift_fst_ι I hI]

/-- The restriction of the projection of the base change scheme over the affine open of a chart
is a thickening. -/
theorem isThickening_morphismRestrict_pullbackProj :
    Stacks.Thickenings.IsThickening (pullbackProj I hI hC h𝔛 (φ := φ) ∣_ p.V) := by
  rw [morphismRestrict_pullbackProj]
  exact Stacks.Thickenings.isThickening_comp (Stacks.Thickenings.isThickening_of_isIso _)
    (p.isThickening_piece_fst I hI)

end PullbackChart

/-- **The projection of the base change scheme is a thickening**: being a closed immersion and
being surjective are local on the target, and over the affine opens of the charts the projection is
the base change of a thickening. -/
theorem isThickening_pullbackProj :
    Stacks.Thickenings.IsThickening (pullbackProj I hI hC h𝔛 (φ := φ)) := by
  obtain ⟨c, hc⟩ := PullbackChart.exists_pullbackChart_mem (φ := φ) h𝔛
  have hcov : iSup (fun q => (c q).V) = ⊤ :=
    iSup_eq_top_of_forall_exists_mem _ fun q => ⟨q, hc q⟩
  exact ⟨IsZariskiLocalAtTarget.of_iSup_eq_top _ hcov fun q =>
    ((c q).isThickening_morphismRestrict_pullbackProj I hI hC h𝔛).1,
    (IsZariskiLocalAtTarget.of_iSup_eq_top (P := @Surjective) _ hcov fun q =>
      (⟨((c q).isThickening_morphismRestrict_pullbackProj I hI hC h𝔛).2⟩ : Surjective _)).surj⟩

end Pullback

section Thickening

variable {𝔛 : McQuillanFormalScheme.{u}} (I : IdealSheaf 𝔛.obj)
  (hI : I.IsWeakIdealOfDefinitionOn (IsWeakAffineFormalOpen 𝔛.obj))
  (hC : I.IsCutOutOn (IsWeakAffineFormalOpen 𝔛.obj)) (h𝔛 : IsMcQuillanFormalScheme 𝔛.obj)

/-- A morphism `h_T → h_𝔛` acts by precomposition on its own point. -/
theorem mcQuillanPoints_app_hom {T T' : Scheme.{u}}
    (t : yoneda.obj T ⟶ mcQuillanFormalSchemePoints 𝔛) (y : T' ⟶ T) :
    (t.app (op T') y).hom = schemeToLTRS.map y ≫ (yonedaEquiv t).hom := by
  rw [← map_yonedaEquiv]
  rfl

/-- **Stacks 0AIV: `(𝔛, 𝒪_𝔛/ℐ) → h_𝔛` is a thickening.** For a weak ideal of definition `ℐ` cut out
by its sections over the weak affine formal opens, the morphism `h_{(𝔛, 𝒪_𝔛/ℐ)} → h_𝔛` is
representable, and its base change along every point `T → 𝔛` of a scheme is a thickening of schemes
`W → T`. -/
theorem isThickening_presheaf_quotientMorphism :
    MorphismProperty.presheaf (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u})
      (I.quotientMorphism hI hC h𝔛) := by
  have : MorphismProperty.RespectsIso
      (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
      (P := (@Stacks.Thickenings.IsThickening : MorphismProperty Scheme.{u}))
  refine MorphismProperty.relative.of_exists fun T t => ?_
  set φ := (yonedaEquiv t).hom
  obtain ⟨k₀, hk₀, -⟩ := I.existsUnique_quotientPoint_factor hI hC h𝔛
    (schemeToLTRS.map (pullbackProj I hI hC h𝔛 (φ := φ)) ≫ φ) (kills_pullbackProj I hI hC h𝔛)
  refine ⟨pullbackScheme I hI hC (φ := φ), yoneda.map k₀, pullbackProj I hI hC h𝔛 (φ := φ), ?_,
    isThickening_pullbackProj I hI hC h𝔛⟩
  refine IsPullback.of_forall_isPullback_app fun T' => ?_
  induction T' using Opposite.rec with
  | op T' =>
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext a
    refine InducedCategory.hom_ext ?_
    change ((I.quotientMorphism hI hC h𝔛).app (op T') (a ≫ k₀)).hom =
      (t.app (op T') (a ≫ pullbackProj I hI hC h𝔛)).hom
    rw [quotientMorphism_app_hom, mcQuillanPoints_app_hom]
    refine (schemeToLTRS_map_comp_assoc _ _ _).trans ?_
    refine (congrArg (schemeToLTRS.map a ≫ ·) hk₀).trans ?_
    exact (schemeToLTRS_map_comp_assoc _ _ _).symm
  · rintro (a₁ : T' ⟶ _) (a₂ : T' ⟶ _) ⟨-, h₂⟩
    have := mono_pullbackProj I hI hC h𝔛 (φ := φ)
    exact (cancel_mono (pullbackProj I hI hC h𝔛 (φ := φ))).mp h₂
  · intro (x : T' ⟶ I.quotientScheme hI hC) (y : T' ⟶ T) hxy
    have hxy' : schemeToLTRS.map x ≫ I.quotientPoint hI hC h𝔛 = schemeToLTRS.map y ≫ φ := by
      have := congrArg (fun z => z.hom) hxy
      simp only at this
      rwa [quotientMorphism_app_hom, mcQuillanPoints_app_hom] at this
    have hy : I.Kills (schemeToLTRS.map y ≫ φ) :=
      hxy' ▸ (I.kills_quotientPoint hI hC h𝔛).comp _
    obtain ⟨m, hm, -⟩ := existsUnique_pullbackProj_factor I hI hC h𝔛 y hy
    refine ⟨m, ?_, hm⟩
    obtain ⟨k₁, -, huniq⟩ := I.existsUnique_quotientPoint_factor hI hC h𝔛
      (schemeToLTRS.map y ≫ φ) hy
    refine (huniq (m ≫ k₀) ?_).trans (huniq x hxy').symm
    refine (schemeToLTRS_map_comp_assoc _ _ _).trans ?_
    refine (congrArg (schemeToLTRS.map m ≫ ·) hk₀).trans ?_
    refine (schemeToLTRS_map_comp_assoc _ _ _).symm.trans ?_
    exact congrArg (fun z => schemeToLTRS.map z ≫ φ) hm

/-- Two ideal sheaves with the same ideals of sections are equal. -/
theorem ext_ideal {X : LTRS.{u}} {I J : IdealSheaf X} (h : ∀ V, I.ideal V = J.ideal V) : I = J := by
  cases I
  cases J
  congr
  exact funext h

include hC in
/-- For an ideal sheaf cut out by its sections over the weak affine formal opens, a point of a
scheme landing in a weak affine formal open `U` and killing `ℐ(U)` kills `ℐ`. -/
theorem kills_of_isCutOutOn {T : Scheme.{u}} (f : schemeToLTRSObj T ⟶ 𝔛.obj) {U : Opens 𝔛.obj}
    (hU : IsWeakAffineFormalOpen 𝔛.obj U) (hf : Set.range f.toHom.base ⊆ (U : Set 𝔛.obj))
    (hkill : ∀ t ∈ I.ideal U, (f.toHom.c.app (op U)).1 t = 0) : I.Kills f :=
  kills_of_range_subset I f hf fun V hVU s hs =>
    mem_ker_iff.mpr (((hC U hU V hVU s).mp hs) T f hf hkill)

/-- **The kernel ideal sheaf of `(𝔛, 𝒪_𝔛/ℐ) → 𝔛` is `ℐ`.** A section in the kernel is, near every
point, a section over an open inside a weak affine formal open `U`; every point landing in `U` and
killing `ℐ(U)` kills `ℐ`, hence factors through `(𝔛, 𝒪_𝔛/ℐ)`, hence kills the section, so the
section lies in `ℐ` because `ℐ` is cut out by its sections over `U`. -/
theorem ker_quotientPoint : ker (I.quotientPoint hI hC h𝔛) = I := by
  refine ext_ideal fun V => le_antisymm (fun s hs => ?_) (I.kills_quotientPoint hI hC h𝔛 V)
  refine I.mem_of_locally_mem fun x hx => ?_
  obtain ⟨U, hxU, hU⟩ := (isMcQuillanFormalScheme_iff_forall_isWeakAffineFormalOpen _).mp h𝔛 x
  refine ⟨V ⊓ U, inf_le_left, ⟨hx, hxU⟩, ?_⟩
  have hs' := (ker (I.quotientPoint hI hC h𝔛)).map_mem (inf_le_left : V ⊓ U ≤ V) hs
  refine (hC U hU (V ⊓ U) inf_le_right _).mpr fun T f hf hkill => ?_
  obtain ⟨k, rfl, -⟩ := I.existsUnique_quotientPoint_factor hI hC h𝔛 f
    (I.kills_of_isCutOutOn hC f hU hf hkill)
  exact mem_ker_iff.mp (ker_le_ker_comp _ _ _ hs')

end Thickening

end AlgebraicGeometry.LocallyTopologicallyRingedSpace.IdealSheaf

end
