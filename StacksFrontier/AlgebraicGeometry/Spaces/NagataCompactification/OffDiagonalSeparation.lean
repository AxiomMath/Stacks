module

public import StacksFrontier.AlgebraicGeometry.Spaces.NagataCompactification.OffDiagonalBoundary
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCompactificationProperExtension
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupStrictTransformSeparation
public import StacksFrontier.AlgebraicGeometry.Spaces.AdmissibleBlowupDominating
public import StacksFrontier.AlgebraicGeometry.Spaces.BlowupPropernessReesChart
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianOfFiniteTypeOverIntegers
public import StacksFrontier.AlgebraicGeometry.Spaces.FittingGeneratorOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.SurfaceTransfer.DominatingNormalizationReduction

/-!
# Separating the off-diagonal of an étale extension by admissible blowups

Let `π : X ⟶ Y` be proper over a Noetherian algebraic space `Y`, `ι : V ⟶ X` an open immersion
and `ψ : V ⟶ U` proper with `ψ ≫ q = ι ≫ π`. Let `j : U₁ ⟶ V` be an open immersion such that
`f = j ≫ ψ` is étale and an isomorphism over the reduced closed subspace on a closed set
`Z ⊆ |U|`. This is the situation of the repaired proof of Stacks 0F4B after Stacks 0F4A, with
`X = X₁`, `V = V₁` and `Z = Z₁`.

The repair modifies `X` by `V`-admissible blowups until the off-diagonal part `O` of
`U₁ ×_U U₁`, seen in `X ×_Y X`, has closure meeting the boundary in no pair of points of a
closed set `R` containing the closure of `f⁻¹ Z`:

* (R0) the closures of `f⁻¹ Z` and `V ∖ U₁` are separated by Stacks 0F46, part (2);
* (R1) `X` is blown up along `D ∩ ∂⁽ᴹ⁾`, where `D` is the closure of `f⁻¹ Z`, `∂ = X ∖ V`, and
  `M` comes from the Nullstellensatz on the closure of `O`; `R` is the complement of the
  coincidence locus of the inverse image of `D` and the exceptional divisor;
* (R2) the closures of `f⁻¹ Z` and `∂ ∖ R` are separated by Stacks 0F46, part (2), on the open
  `X ∖ (R ∩ ∂)`.

## Main results

* `AlgebraicGeometry.Space.isFinitePresentation_ι_of_isNoetherian`: closed subspaces of a
  Noetherian algebraic space are of finite presentation.
* `AlgebraicGeometry.Space.exists_isOpenImmersion_lift_of_isBlowupAlong`: an open immersion
  lifts across a blowup whose centre it misses.
* `AlgebraicGeometry.Space.exists_isAdmissibleBlowup_disjoint_closure_image`: Stacks 0F46,
  part (2), along an open immersion (step R0).
* `AlgebraicGeometry.Space.subspacePointSet_infinitesimalNeighbourhood_subset`: the
  infinitesimal neighbourhoods of a closed subspace have no new points.
* `AlgebraicGeometry.Space.exists_isAdmissibleBlowup_offDiagonal_separated`: step R1.
* `AlgebraicGeometry.Space.exists_isAdmissibleBlowup_disjoint_closure_boundary`: step R2, which
  separates the closure of `f⁻¹ Z` from the part of the boundary outside `R`.

## References

* [Stacks Project, Tag 0F4B](https://stacks.math.columbia.edu/tag/0F4B)
* [Stacks Project, Tag 0F46](https://stacks.math.columbia.edu/tag/0F46)
-/
@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] pointTopology

/-- **Closed subspaces of a Noetherian algebraic space are of finite presentation.** The ideal
of the closed subspace on an affine open of the atlas is an ideal of a Noetherian ring. -/
theorem isFinitePresentation_ι_of_isNoetherian (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hN : IsNoetherian B S hS hZ X.1)
    (Z : ClosedSubspaces B S hS X.1) : IsFinitePresentation B S hS Z.1.ι := by
  rw [isFinitePresentation_ι_iff_fg_chartKer]
  intro A
  have hV : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj (atlasObj B S hS X)) :=
    (exists_atlas_iff_forall_etale B S hS X.1 (fun T : Scheme.{u} => IsLocallyNoetherian T)
      X.2).mp hN.2.2 _ (atlasHom B S hS X) (atlasHom_etale B S hS X)
  have := hV.component_noetherian A
  exact IsNoetherian.noetherian _

/-- For an open embedding `ι` and a closed set `A`, the closure of `ι '' A` meets the range of `ι`
in `ι '' A`. -/
theorem _root_.Topology.IsOpenEmbedding.closure_image_inter_range {α β : Type*}
    [TopologicalSpace α] [TopologicalSpace β] {ι : α → β} (hι : Topology.IsOpenEmbedding ι)
    {A : Set α} (hA : IsClosed A) : closure (ι '' A) ∩ Set.range ι = ι '' A := by
  refine Set.Subset.antisymm ?_ fun x hx => ⟨subset_closure hx, Set.image_subset_range _ _ hx⟩
  rintro _ ⟨hx, y, rfl⟩
  refine ⟨y, ?_, rfl⟩
  rw [← hA.closure_eq, hι.isInducing.closure_eq_preimage_closure_image]
  exact hx

/-- **An open immersion lifts across a blowup with centre off its image.** Let `b : X' ⟶ X` be
the blowup of `X` in a closed subspace `Zc` disjoint from the image of an open immersion
`ι : V ⟶ X`. Then `ι` lifts to an open immersion `ι' : V ⟶ X'` with `ι' ≫ b = ι`, and the
points of `X'` over the image of a set of points of `V` are the image of that set under `ι'`. -/
theorem exists_isOpenImmersion_lift_of_isBlowupAlong {X X' : AlgebraicSpaces B S hS}
    {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hV : IsAlgebraicSpace B S hS V)
    {Zc : ClosedSubspaces B S hS X.1} {b : X' ⟶ X} (hb : IsBlowupAlong B S hS Zc b)
    {ι : V ⟶ X.1} (hι : IsOpenImmersion B S hS ι)
    (hdisj : Disjoint (Set.range (pointsMap B S hS V ι)) (subspacePointSet B S hS X.1 Zc.1)) :
    ∃ ι' : V ⟶ X'.1, ι' ≫ b.hom = ι ∧ IsOpenImmersion B S hS ι' ∧
      ∀ A : Set (points B S hS V),
        pointsMap B S hS _ b.hom ⁻¹' (pointsMap B S hS V ι '' A) = pointsMap B S hS V ι' '' A := by
  have : Mono ι := mono_of_presheaf_isOpenImmersion hι
  obtain ⟨ι', hι'b, hrange⟩ := exists_lift_range_eq_preimage_of_isBlowupAlong hV hb ι
    (by rwa [subspacePointSet_range])
  have : Mono ι' := mono_of_mono_fac hι'b
  have hopen : IsOpenSubspace B S hS (Subfunctor.range ι') := by
    rw [hrange]
    exact isOpenSubspace_preimage B S hS b.hom _ X.2 X'.2
      (isOpenSubspace_subfunctorRange B S hS hV hι)
  have hι'open : IsOpenImmersion B S hS ι' := by
    rw [← Subfunctor.toRange_ι ι']
    exact isOpenImmersion_comp B S hS _ _ (isOpenImmersion_of_isIso B S hS _) hopen.2
  refine ⟨ι', hι'b, hι'open, fun A => Set.Subset.antisymm ?_ ?_⟩
  · intro x hx
    obtain ⟨a, ha, hax⟩ := hx
    have hxr : x ∈ subspacePointSet B S hS X'.1 (Subfunctor.range ι') := by
      rw [hrange, subspacePointSet_preimage, subspacePointSet_range]
      exact ⟨a, hax⟩
    rw [subspacePointSet_range] at hxr
    obtain ⟨a', rfl⟩ := hxr
    refine ⟨a', ?_, rfl⟩
    have : a = a' := pointsMap_injective_of_mono B S hS ι (by
      rw [hax, ← pointsMap_comp_apply, hι'b])
    exact this ▸ ha
  · rintro _ ⟨a, ha, rfl⟩
    exact ⟨a, ha, by rw [← pointsMap_comp_apply, hι'b]⟩

/-- In a Noetherian topological space every closed set is constructible. -/
theorem _root_.IsClosed.isConstructible_of_noetherianSpace {α : Type*} [TopologicalSpace α]
    [TopologicalSpace.NoetherianSpace α] {T : Set α} (hT : IsClosed T) :
    Topology.IsConstructible T :=
  Topology.isConstructible_compl.1 (IsRetrocompact.isConstructible hT.isOpen_compl
    fun _ _ _ => TopologicalSpace.NoetherianSpace.isCompact _)

/-- The map on points of an open immersion into an algebraic space is an open embedding. -/
private theorem isOpenEmbedding_pointsMap_of_isOpenImmersion_presheaf
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : F ⟶ G} (hf : IsOpenImmersion B S hS f) :
    Topology.IsOpenEmbedding (pointsMap B S hS F f) :=
  have : Mono f := mono_of_presheaf_isOpenImmersion hf
  Topology.IsOpenEmbedding.of_continuous_injective_isOpenMap (continuous_pointsMap B S hS _)
    (pointsMap_injective_of_mono B S hS f) (isOpenMap_pointsMap_of_isOpenImmersion B S hS _ hf)

/-- **Separating closed subsets of an open subspace `U` of `X` containing the image of `ι`** by a
`V`-admissible blowup through which `ι` lifts (Stacks 0F46, part (2)). -/
private theorem exists_isAdmissibleBlowup_lift_disjoint_closure
    (hZ : B.Contains (⊤_ Scheme.{u}))
    {X : AlgebraicSpaces B S hS} (hN : IsNoetherian B S hS hZ X.1)
    {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hV : IsAlgebraicSpace B S hS V) {ι : V ⟶ X.1}
    (hι : IsOpenImmersion B S hS ι) (U : OpenSubspaces B S hS X.1)
    (hVU : Set.range (pointsMap B S hS V ι) ⊆ Set.range (pointsMap B S hS _ U.1.ι))
    {T₁ T₂ : Set (points B S hS U.1.toFunctor)} (h₁ : IsClosed T₁) (h₂ : IsClosed T₂)
    (hdisj : Disjoint T₁ T₂) :
    ∃ (X' : AlgebraicSpaces B S hS) (b : X' ⟶ X) (ι' : V ⟶ X'.1),
      IsAdmissibleBlowup B S hS ⟨Subfunctor.range ι, isOpenSubspace_subfunctorRange B S hS hV hι⟩
        b ∧ ι' ≫ b.hom = ι ∧ IsOpenImmersion B S hS ι' ∧
      (∀ A : Set (points B S hS V),
        pointsMap B S hS _ b.hom ⁻¹' (pointsMap B S hS V ι '' A) = pointsMap B S hS V ι' '' A) ∧
      Disjoint (closure (pointsMap B S hS _ b.hom ⁻¹' (pointsMap B S hS _ U.1.ι '' T₁)))
        (closure (pointsMap B S hS _ b.hom ⁻¹' (pointsMap B S hS _ U.1.ι '' T₂))) := by
  have : Mono ι := mono_of_presheaf_isOpenImmersion hι
  have : TopologicalSpace.NoetherianSpace (points B S hS X.1) :=
    noetherianSpace_of_isQuasiCompact_of_isLocallyNoetherian B S hS X.1 X.2 hN.1 hN.2.2
  have : TopologicalSpace.NoetherianSpace (points B S hS U.1.toFunctor) :=
    (isOpenEmbedding_pointsMap_of_isOpenImmersion_presheaf U.2.2).isInducing.noetherianSpace
  have hUqc : IsQuasiCompactSpace B S hS U.1.toFunctor :=
    (isQuasiCompactSpace_iff_compactSpace_points B S hS _ U.2.1).2 inferInstance
  obtain ⟨X', b, hb, hcl⟩ := exists_isAdmissibleBlowup_disjoint_closure hZ hN.1 hN.2.1 U hUqc
    _ _ h₁ h₂ h₁.isConstructible_of_noetherianSpace h₂.isConstructible_of_noetherianSpace hdisj
  obtain ⟨Zc, hZfp, hZdisj, hbl⟩ := hb
  have hZV : Disjoint (Set.range (pointsMap B S hS V ι)) (subspacePointSet B S hS X.1 Zc.1) :=
    Set.disjoint_of_subset_left hVU hZdisj
  obtain ⟨ι', hι'b, hι'open, hpre⟩ := exists_isOpenImmersion_lift_of_isBlowupAlong hV hbl hι hZV
  exact ⟨X', b, ι', ⟨Zc, hZfp, by rwa [subspacePointSet_range], hbl⟩, hι'b, hι'open, hpre, hcl⟩

/-- **Separating two closed subsets of an open subspace by an admissible blowup** (Stacks 0F46,
part (2), along an open immersion). Let `X` be a Noetherian algebraic space, `ι : V ⟶ X` an open
immersion and `A₁, A₂` disjoint closed sets of points of `V`. There is a `V`-admissible blowup
`b : X' ⟶ X`, through which `ι` lifts to an open immersion `ι'`, such that the closures in `X'`
of `ι' '' A₁` and `ι' '' A₂` are disjoint. -/
theorem exists_isAdmissibleBlowup_disjoint_closure_image (hZ : B.Contains (⊤_ Scheme.{u}))
    {X : AlgebraicSpaces B S hS} (hN : IsNoetherian B S hS hZ X.1)
    {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hV : IsAlgebraicSpace B S hS V) {ι : V ⟶ X.1}
    (hι : IsOpenImmersion B S hS ι) {A₁ A₂ : Set (points B S hS V)} (h₁ : IsClosed A₁)
    (h₂ : IsClosed A₂) (hdisj : Disjoint A₁ A₂) :
    ∃ (X' : AlgebraicSpaces B S hS) (b : X' ⟶ X) (ι' : V ⟶ X'.1),
      IsAdmissibleBlowup B S hS ⟨Subfunctor.range ι, isOpenSubspace_subfunctorRange B S hS hV hι⟩
        b ∧ ι' ≫ b.hom = ι ∧ IsOpenImmersion B S hS ι' ∧
      (∀ A : Set (points B S hS V),
        pointsMap B S hS _ b.hom ⁻¹' (pointsMap B S hS V ι '' A) = pointsMap B S hS V ι' '' A) ∧
      Disjoint (closure (pointsMap B S hS V ι' '' A₁)) (closure (pointsMap B S hS V ι' '' A₂)) := by
  have : Mono ι := mono_of_presheaf_isOpenImmersion hι
  set U : OpenSubspaces B S hS X.1 :=
    ⟨Subfunctor.range ι, isOpenSubspace_subfunctorRange B S hS hV hι⟩ with hUdef
  have hιemb := isOpenEmbedding_pointsMap_of_isOpenImmersion_presheaf hι
  have hrange : Set.range (pointsMap B S hS _ U.1.ι) = Set.range (pointsMap B S hS V ι) :=
    range_pointsMap_ι_range B S hS ι
  -- the traces on `U` of the images of `A₁` and `A₂`
  have htrace : ∀ A : Set (points B S hS V), IsClosed A →
      IsClosed (pointsMap B S hS _ U.1.ι ⁻¹' (pointsMap B S hS V ι '' A)) ∧
        pointsMap B S hS _ U.1.ι '' (pointsMap B S hS _ U.1.ι ⁻¹' (pointsMap B S hS V ι '' A)) =
          pointsMap B S hS V ι '' A := by
    intro A hA
    refine ⟨?_, ?_⟩
    · have : pointsMap B S hS _ U.1.ι ⁻¹' (pointsMap B S hS V ι '' A) =
          pointsMap B S hS _ U.1.ι ⁻¹' closure (pointsMap B S hS V ι '' A) := by
        ext x
        refine ⟨fun hx => subset_closure hx, fun hx => ?_⟩
        rw [← hιemb.closure_image_inter_range hA]
        exact ⟨hx, hrange ▸ ⟨x, rfl⟩⟩
      rw [this]
      exact isClosed_closure.preimage (continuous_pointsMap B S hS _)
    · rw [Set.image_preimage_eq_inter_range, hrange]
      exact Set.inter_eq_left.2 (Set.image_subset_range _ _)
  obtain ⟨hT₁, hT₁'⟩ := htrace A₁ h₁
  obtain ⟨hT₂, hT₂'⟩ := htrace A₂ h₂
  obtain ⟨X', b, ι', hb, hι'b, hι'open, hpre, hcl⟩ :=
    exists_isAdmissibleBlowup_lift_disjoint_closure hZ hN hV hι U hrange.ge hT₁ hT₂
    (by
      rw [Set.disjoint_iff]
      rintro x ⟨⟨a₁, ha₁, hx₁⟩, ⟨a₂, ha₂, hx₂⟩⟩
      have := pointsMap_injective_of_mono B S hS ι (hx₁.trans hx₂.symm)
      exact Set.disjoint_iff.1 hdisj ⟨ha₁, this ▸ ha₂⟩)
  refine ⟨X', b, ι', hb, hι'b, hι'open, hpre, ?_⟩
  rw [← hpre, ← hpre, ← hT₁', ← hT₂']
  exact hcl

/-- **An infinitesimal neighbourhood has the same points.** The points of `Y⁽ⁿ⁾` are points of
`Y`: where the ideal of `Y` is the unit ideal on an affine chart, so is its `n`-th power. -/
theorem subspacePointSet_infinitesimalNeighbourhood_subset (X : AlgebraicSpaces B S hS)
    (Y : ClosedSubspaces B S hS X.1) (n : ℕ) :
    subspacePointSet B S hS X.1 (infinitesimalNeighbourhood B S hS X Y n).1 ⊆
      subspacePointSet B S hS X.1 Y.1 := by
  intro x hx
  change x ∈ Set.range (pointsMap B S hS _ (infinitesimalNeighbourhood B S hS X Y n).1.ι) at hx
  change x ∈ Set.range (pointsMap B S hS _ Y.1.ι)
  rw [range_pointsMap_ι_eq_idealZeroLocus] at hx ⊢
  intro hxu
  obtain ⟨U, hUaff, hU, hxU⟩ := exists_affine_chart_obj_eq_top_of_mem_idealUnitLocus B S hS X _ hxu
  refine hx ⟨U, ?_, hxU⟩
  rw [definingIdealSheaf_infinitesimalNeighbourhood]
  have := idealPow_obj_eq_pow_of_isAffine B S hS X.1 X.2 (definingIdealSheaf B S hS X Y)
    (isQuasicoherentOnSite_definingIdealSheaf B S hS X Y) n hUaff
  change chartSectionIdeal B S hS X.1 X.2 _ U = ⊤
  rw [this]
  rw [show chartSectionIdeal B S hS X.1 X.2 (definingIdealSheaf B S hS X Y) U = ⊤ from hU,
    Ideal.top_pow]

/-- The fibre product `X ×_Y X` of a proper `π : X ⟶ Y` is proper over `Y`. -/
theorem isProper_pullback_fst_comp {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {π : X ⟶ Y}
    (hπ : IsProper B S hS π) : IsProper B S hS (pullback.fst π π ≫ π) :=
  isProper_comp B S hS (isAlgebraicSpace_pullback B S hS π π hX hX hY) hX hY _ _
    (isProper_pullback_fst B S hS hX hY hX π π hπ) hπ

section Repair

variable {X Y : AlgebraicSpaces B S hS} {π : X ⟶ Y} {V U U₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {ι : V ⟶ X.1} {ψ : V ⟶ U} {q : U ⟶ Y.1} {j : U₁ ⟶ V}

/-- **The off-diagonal points are closed among the points with coordinates in `U₁`**, as an
equality of sets. -/
theorem offDiagonal_eq_closure_inter (hV : IsAlgebraicSpace B S hS V)
    (hU : IsAlgebraicSpace B S hS U) (hU₁ : IsAlgebraicSpace B S hS U₁) (hψ : IsProper B S hS ψ)
    (hπ : IsSeparated B S hS π.hom) (hι : IsOpenImmersion B S hS ι)
    (hj : IsOpenImmersion B S hS j) (h : ψ ≫ q = ι ≫ π.hom) (hf : IsEtale B S hS (j ≫ ψ))
    {ρ : pullback (j ≫ ψ) (j ≫ ψ) ⟶ pullback π.hom π.hom}
    (hρ₁ : ρ ≫ pullback.fst π.hom π.hom = pullback.fst (j ≫ ψ) (j ≫ ψ) ≫ j ≫ ι)
    (hρ₂ : ρ ≫ pullback.snd π.hom π.hom = pullback.snd (j ≫ ψ) (j ≫ ψ) ≫ j ≫ ι) :
    pointsMap B S hS _ ρ '' (Set.range (pointsMap B S hS U₁ (pullback.diagonal (j ≫ ψ))))ᶜ =
      closure (pointsMap B S hS _ ρ ''
        (Set.range (pointsMap B S hS U₁ (pullback.diagonal (j ≫ ψ))))ᶜ) ∩
      (pointsMap B S hS _ (pullback.fst π.hom π.hom) ⁻¹'
          Set.range (pointsMap B S hS U₁ (j ≫ ι)) ∩
        pointsMap B S hS _ (pullback.snd π.hom π.hom) ⁻¹'
          Set.range (pointsMap B S hS U₁ (j ≫ ι))) := by
  refine Set.Subset.antisymm (fun w hw => ⟨subset_closure hw, ?_⟩) fun w hw =>
    mem_offDiagonal_of_mem_closure hρ₁ hρ₂ hV hU hψ hπ hι h hU₁ hj hf hw.1 hw.2.1 hw.2.2
  obtain ⟨k, -, rfl⟩ := hw
  exact ⟨⟨pointsMap B S hS _ (pullback.fst (j ≫ ψ) (j ≫ ψ)) k, by
      rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, hρ₁]⟩,
    ⟨pointsMap B S hS _ (pullback.snd (j ≫ ψ) (j ≫ ψ)) k, by
      rw [← pointsMap_comp_apply, ← pointsMap_comp_apply, hρ₂]⟩⟩

/-- **Off-diagonal points upstairs.** Let `β : X' ⟶ X`, `ι'` a lift of `ι` and
`ρ₀ : X' ×_Y X' ⟶ X ×_Y X` the map `β × β`. If every point `w'` of `X' ×_Y X'` over the closure of
the off-diagonal points `O` of `X ×_Y X` and in the closure of `ρ₀⁻¹ O` has a coordinate in `Ω`,
then so has every point in the closure of the off-diagonal points of `X' ×_Y X'`. -/
theorem mem_or_of_mem_closure_offDiagonal_of_comp {X' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {β : X' ⟶ X.1} {π' : X' ⟶ Y.1} {ι' : V ⟶ X'} (hι'β : ι' ≫ β = ι)
    {ρ : pullback (j ≫ ψ) (j ≫ ψ) ⟶ pullback π.hom π.hom}
    (hρ₁ : ρ ≫ pullback.fst π.hom π.hom = pullback.fst (j ≫ ψ) (j ≫ ψ) ≫ j ≫ ι)
    (hρ₂ : ρ ≫ pullback.snd π.hom π.hom = pullback.snd (j ≫ ψ) (j ≫ ψ) ≫ j ≫ ι)
    {ρ₀ : pullback π' π' ⟶ pullback π.hom π.hom}
    (h₀₁ : ρ₀ ≫ pullback.fst π.hom π.hom = pullback.fst π' π' ≫ β)
    (h₀₂ : ρ₀ ≫ pullback.snd π.hom π.hom = pullback.snd π' π' ≫ β)
    {Ω : Set (points B S hS X')}
    (hM : ∀ w' : points B S hS (pullback π' π'),
      pointsMap B S hS _ ρ₀ w' ∈ closure (pointsMap B S hS _ ρ ''
        (Set.range (pointsMap B S hS U₁ (pullback.diagonal (j ≫ ψ))))ᶜ) →
      w' ∈ closure (pointsMap B S hS (pullback π' π') ρ₀ ⁻¹' (pointsMap B S hS _ ρ ''
        (Set.range (pointsMap B S hS U₁ (pullback.diagonal (j ≫ ψ))))ᶜ)) →
      pointsMap B S hS _ (pullback.fst π' π') w' ∈ Ω ∨
        pointsMap B S hS _ (pullback.snd π' π') w' ∈ Ω)
    {ρ' : pullback (j ≫ ψ) (j ≫ ψ) ⟶ pullback π' π'}
    (hρ'₁ : ρ' ≫ pullback.fst π' π' = pullback.fst (j ≫ ψ) (j ≫ ψ) ≫ j ≫ ι')
    (hρ'₂ : ρ' ≫ pullback.snd π' π' = pullback.snd (j ≫ ψ) (j ≫ ψ) ≫ j ≫ ι')
    {w : points B S hS (pullback π' π')}
    (hw : w ∈ closure (pointsMap B S hS _ ρ' ''
      (Set.range (pointsMap B S hS U₁ (pullback.diagonal (j ≫ ψ))))ᶜ)) :
    pointsMap B S hS _ (pullback.fst π' π') w ∈ Ω ∨
      pointsMap B S hS _ (pullback.snd π' π') w ∈ Ω := by
  have hcomp : ρ' ≫ ρ₀ = ρ := by
    apply pullback.hom_ext
    · rw [Category.assoc, h₀₁, ← Category.assoc, hρ'₁, hρ₁, Category.assoc, Category.assoc,
        hι'β]
    · rw [Category.assoc, h₀₂, ← Category.assoc, hρ'₂, hρ₂, Category.assoc, Category.assoc,
        hι'β]
  have hmaps : Set.MapsTo (pointsMap B S hS _ ρ₀)
      (pointsMap B S hS _ ρ' '' (Set.range (pointsMap B S hS U₁ (pullback.diagonal (j ≫ ψ))))ᶜ)
      (pointsMap B S hS _ ρ '' (Set.range (pointsMap B S hS U₁ (pullback.diagonal (j ≫ ψ))))ᶜ) := by
    rintro _ ⟨k, hk, rfl⟩
    exact ⟨k, hk, by rw [← pointsMap_comp_apply, hcomp]⟩
  exact hM w (map_mem_closure (continuous_pointsMap B S hS _) hw hmaps)
    (closure_mono hmaps.subset_preimage hw)

/-- **The off-diagonal after the blowup along `D ∩ ∂⁽ᴹ⁾`.** In the situation of
`AlgebraicGeometry.Space.notMem_range_of_mem_closure_offDiagonal`, with `π` proper over a
Noetherian `Y`, let `Ob`, `D` and `Yb` be closed subspaces whose points are the closure of the
off-diagonal points, the closure of the image `T` of `f⁻¹ Z`, and the boundary `X ∖ V`. There is
`M` such that for every blowup `β` along `D ∩ Yb⁽ᴹ⁾` with `β ≫ π` proper and every lift `ι'` of
`ι`, each point of the closure of the off-diagonal points of `X' ×_Y X'` has a coordinate in the
coincidence locus of `β⁻¹ D` and `β⁻¹(D ∩ Yb⁽ᴹ⁾)`. This is
`AlgebraicGeometry.Space.exists_mem_coincidenceLocus_or_of_isBlowupAlong` on `X' ×_Y X'`. -/
theorem exists_forall_isBlowupAlong_mem_coincidenceLocus (hZ : B.Contains (⊤_ Scheme.{u}))
    (hπ : IsProper B S hS π.hom) (hYN : IsNoetherian B S hS hZ Y.1)
    (hV : IsAlgebraicSpace B S hS V) (hU : IsAlgebraicSpace B S hS U)
    (hU₁ : IsAlgebraicSpace B S hS U₁) (hψ : IsProper B S hS ψ) (hι : IsOpenImmersion B S hS ι)
    (hj : IsOpenImmersion B S hS j) (h : ψ ≫ q = ι ≫ π.hom) (hf : IsEtale B S hS (j ≫ ψ))
    (Zs : Set (points B S hS U)) (hZs : IsClosed Zs)
    (hiso : IsIso ((reducedClosedSubspace B S hS U hU Zs hZs).fromPreimage (j ≫ ψ)))
    {ρ : pullback (j ≫ ψ) (j ≫ ψ) ⟶ pullback π.hom π.hom}
    (hρ₁ : ρ ≫ pullback.fst π.hom π.hom = pullback.fst (j ≫ ψ) (j ≫ ψ) ≫ j ≫ ι)
    (hρ₂ : ρ ≫ pullback.snd π.hom π.hom = pullback.snd (j ≫ ψ) (j ≫ ψ) ≫ j ≫ ι)
    (Ob : ClosedSubspaces B S hS (pullback π.hom π.hom))
    (hOb : subspacePointSet B S hS _ Ob.1 = closure (pointsMap B S hS _ ρ ''
      (Set.range (pointsMap B S hS U₁ (pullback.diagonal (j ≫ ψ))))ᶜ))
    (D Yb : ClosedSubspaces B S hS X.1)
    (hD : subspacePointSet B S hS _ D.1 =
      closure (pointsMap B S hS U₁ (j ≫ ι) '' (pointsMap B S hS U₁ (j ≫ ψ) ⁻¹' Zs)))
    (hYb : subspacePointSet B S hS _ Yb.1 = (Set.range (pointsMap B S hS V ι))ᶜ) :
    ∃ M : ℕ, ∀ {X' : AlgebraicSpaces B S hS} (β : X' ⟶ X),
      IsBlowupAlong B S hS (schemeTheoreticIntersection B S hS X.1 X.2 D
        (infinitesimalNeighbourhood B S hS X Yb M)) β →
      ∀ (π' : X'.1 ⟶ Y.1), β.hom ≫ π.hom = π' → IsProper B S hS π' →
      ∀ (ι' : V ⟶ X'.1), ι' ≫ β.hom = ι →
      ∀ ρ' : pullback (j ≫ ψ) (j ≫ ψ) ⟶ pullback π' π',
        ρ' ≫ pullback.fst π' π' = pullback.fst (j ≫ ψ) (j ≫ ψ) ≫ j ≫ ι' →
        ρ' ≫ pullback.snd π' π' = pullback.snd (j ≫ ψ) (j ≫ ψ) ≫ j ≫ ι' →
        ∀ w ∈ closure (pointsMap B S hS _ ρ' ''
            (Set.range (pointsMap B S hS U₁ (pullback.diagonal (j ≫ ψ))))ᶜ),
          pointsMap B S hS _ (pullback.fst π' π') w ∈ coincidenceLocus B S hS X'
              (preimageClosedSubspace β D) (preimageClosedSubspace β
                (schemeTheoreticIntersection B S hS X.1 X.2 D
                  (infinitesimalNeighbourhood B S hS X Yb M))) ∨
            pointsMap B S hS _ (pullback.snd π' π') w ∈ coincidenceLocus B S hS X'
              (preimageClosedSubspace β D) (preimageClosedSubspace β
                (schemeTheoreticIntersection B S hS X.1 X.2 D
                  (infinitesimalNeighbourhood B S hS X Yb M))) := by
  have hP : IsAlgebraicSpace B S hS (pullback π.hom π.hom) :=
    isAlgebraicSpace_pullback B S hS π.hom π.hom X.2 X.2 Y.2
  have hPN : IsNoetherian B S hS hZ (pullback π.hom π.hom) :=
    isNoetherian_of_isProper hZ hP Y.2 hYN _ (isProper_pullback_fst_comp X.2 Y.2 hπ)
  have hjιopen : IsOpen (Set.range (pointsMap B S hS U₁ (j ≫ ι))) :=
    isOpen_range_pointsMap_of_isOpenImmersion B S hS _ (isOpenImmersion_comp B S hS _ _ hj hι)
  obtain ⟨M, hM⟩ := exists_mem_coincidenceLocus_or_of_isBlowupAlong hZ π Ob
    (isNoetherian_closedSubfunctor B S hS hZ ⟨_, hP⟩ hPN Ob.2) D Yb
    (fun w hw h₁ h₂ => by
      rw [hOb] at hw
      rw [hD] at h₁ h₂
      rw [hYb]
      exact notMem_range_of_mem_closure_offDiagonal hρ₁ hρ₂ hV hU hψ hπ.isSeparated hι h hU₁ hj
        hf Zs hZs hiso hw h₁ h₂)
    (O := pointsMap B S hS _ ρ ''
      (Set.range (pointsMap B S hS U₁ (pullback.diagonal (j ≫ ψ))))ᶜ)
    (A := pointsMap B S hS _ (pullback.fst π.hom π.hom) ⁻¹'
          Set.range (pointsMap B S hS U₁ (j ≫ ι)) ∩
        pointsMap B S hS _ (pullback.snd π.hom π.hom) ⁻¹'
          Set.range (pointsMap B S hS U₁ (j ≫ ι)))
    ((hjιopen.preimage (continuous_pointsMap B S hS _)).inter
      (hjιopen.preimage (continuous_pointsMap B S hS _)))
    (by
      rw [hOb]
      exact offDiagonal_eq_closure_inter hV hU hU₁ hψ hπ.isSeparated hι hj h hf hρ₁ hρ₂)
    (fun w hw => by
      rw [hD]
      exact fst_notMem_closure_of_mem_offDiagonal hρ₁ hV hU hψ hι hU₁ hj Zs hZs hiso hw)
    (fun w hw => by
      rw [hD]
      exact snd_notMem_closure_of_mem_offDiagonal hρ₁ hρ₂ hV hU hψ hι hU₁ hj Zs hZs hiso hw)
  refine ⟨M, fun {X'} β hβ π' hπ' hπ'p ι' hι'β ρ' hρ'₁ hρ'₂ w hw => ?_⟩
  have hP' : IsAlgebraicSpace B S hS (pullback π' π') :=
    isAlgebraicSpace_pullback B S hS _ _ X'.2 X'.2 Y.2
  refine mem_or_of_mem_closure_offDiagonal_of_comp hι'β hρ₁ hρ₂
    (ρ₀ := pullback.map π' π' π.hom π.hom β.hom β.hom (𝟙 Y.1)
      (by rw [Category.comp_id, hπ']) (by rw [Category.comp_id, hπ']))
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) (fun w' h₁ h₂ => ?_) hρ'₁ hρ'₂ hw
  rw [← hOb] at h₁
  exact hM β hβ hP'
    (isNoetherian_of_isProper hZ hP' Y.2 hYN _ (isProper_pullback_fst_comp X'.2 Y.2 hπ'p))
    (pullback.fst _ _) (pullback.snd _ _) _ (pullback.lift_fst _ _ _)
    (pullback.lift_snd _ _ _) w' h₁ h₂

/-- **The image of `f⁻¹ Z` after the blowup avoids the coincidence locus.** Let `β : X' ⟶ X`,
`ι'` a lift of `ι`, and `D`, `Zc` closed subspaces of `X` with the image `T` of `f⁻¹ Z` in `|D|`
and `Zc` disjoint from `V`. Then the closure of the image of `f⁻¹ Z` in `X'` lies outside the
coincidence locus of `β⁻¹ D` and `β⁻¹ Zc`: those points lie in `β⁻¹ D` and not in `β⁻¹ Zc`. -/
theorem closure_image_subset_compl_coincidenceLocus {X' : AlgebraicSpaces B S hS} (β : X' ⟶ X)
    {ι' : V ⟶ X'.1} (hι'β : ι' ≫ β.hom = ι) (Zs : Set (points B S hS U))
    (D Zc : ClosedSubspaces B S hS X.1)
    (hTD : pointsMap B S hS U₁ (j ≫ ι) '' (pointsMap B S hS U₁ (j ≫ ψ) ⁻¹' Zs) ⊆
      subspacePointSet B S hS X.1 D.1)
    (hZcV : Disjoint (Set.range (pointsMap B S hS V ι)) (subspacePointSet B S hS X.1 Zc.1)) :
    closure (pointsMap B S hS U₁ (j ≫ ι') '' (pointsMap B S hS U₁ (j ≫ ψ) ⁻¹' Zs)) ⊆
      (coincidenceLocus B S hS X' (preimageClosedSubspace β D) (preimageClosedSubspace β Zc))ᶜ := by
  refine closure_minimal ?_ (isOpen_coincidenceLocus B S hS X' _ _).isClosed_compl
  rintro _ ⟨y, hy, rfl⟩
  have hβy : pointsMap B S hS _ β.hom (pointsMap B S hS U₁ (j ≫ ι') y) =
      pointsMap B S hS U₁ (j ≫ ι) y := by
    rw [← pointsMap_comp_apply, Category.assoc, hι'β]
  refine subspacePointSet_diff_subset_compl_coincidenceLocus B S hS X' _ _ ⟨?_, ?_⟩
  · change _ ∈ subspacePointSet B S hS X'.1 (D.1.preimage β.hom)
    rw [subspacePointSet_preimage, Set.mem_preimage, hβy]
    exact hTD ⟨y, hy, rfl⟩
  · change _ ∉ subspacePointSet B S hS X'.1 (Zc.1.preimage β.hom)
    rw [subspacePointSet_preimage, Set.mem_preimage, hβy]
    exact Set.disjoint_left.1 hZcV ⟨pointsMap B S hS _ j y, by rw [← pointsMap_comp_apply]⟩

/-- **One admissible blowup separates the off-diagonal from the boundary** (step R1 of the
repaired proof of Stacks 0F4B). Let `π : X ⟶ Y` be proper over a Noetherian `Y`, `ι : V ⟶ X` an
open immersion, `ψ : V ⟶ U` proper with `ψ ≫ q = ι ≫ π`, and `j : U₁ ⟶ V` an open immersion with
`f = j ≫ ψ` étale and an isomorphism over the reduced closed subspace on a closed set
`Z ⊆ |U|`. There are a `V`-admissible blowup `β : X' ⟶ X`, a lift `ι'` of `ι` and a closed set
`R ⊆ |X'|` containing the closure of the image of `f⁻¹ Z`, such that no point of the closure of
the off-diagonal points of `X' ×_Y X'` has both coordinates in `R`.

The blowup is along `D ∩ ∂⁽ᴹ⁾` (`D` the closure of the image of `f⁻¹ Z`, `∂ = X ∖ V`) with `M`
from `AlgebraicGeometry.Space.exists_forall_isBlowupAlong_mem_coincidenceLocus`, and `R` is the
complement of the coincidence locus of `β⁻¹ D` and the exceptional divisor. -/
theorem exists_isAdmissibleBlowup_offDiagonal_separated (hZ : B.Contains (⊤_ Scheme.{u}))
    (hπ : IsProper B S hS π.hom) (hYN : IsNoetherian B S hS hZ Y.1)
    (hV : IsAlgebraicSpace B S hS V) (hU : IsAlgebraicSpace B S hS U)
    (hU₁ : IsAlgebraicSpace B S hS U₁) (hψ : IsProper B S hS ψ) (hι : IsOpenImmersion B S hS ι)
    (hj : IsOpenImmersion B S hS j) (h : ψ ≫ q = ι ≫ π.hom) (hf : IsEtale B S hS (j ≫ ψ))
    (Zs : Set (points B S hS U)) (hZs : IsClosed Zs)
    (hiso : IsIso ((reducedClosedSubspace B S hS U hU Zs hZs).fromPreimage (j ≫ ψ))) :
    ∃ (X' : AlgebraicSpaces B S hS) (β : X' ⟶ X) (ι' : V ⟶ X'.1) (R : Set (points B S hS X'.1)),
      IsAdmissibleBlowup B S hS ⟨Subfunctor.range ι, isOpenSubspace_subfunctorRange B S hS hV hι⟩
        β ∧ ι' ≫ β.hom = ι ∧ IsOpenImmersion B S hS ι' ∧
      (∀ A : Set (points B S hS V),
        pointsMap B S hS _ β.hom ⁻¹' (pointsMap B S hS V ι '' A) = pointsMap B S hS V ι' '' A) ∧
      IsClosed R ∧
      closure (pointsMap B S hS U₁ (j ≫ ι') '' (pointsMap B S hS U₁ (j ≫ ψ) ⁻¹' Zs)) ⊆ R ∧
      ∀ (π' : X'.1 ⟶ Y.1), β.hom ≫ π.hom = π' →
      ∀ ρ' : pullback (j ≫ ψ) (j ≫ ψ) ⟶ pullback π' π',
        ρ' ≫ pullback.fst π' π' = pullback.fst (j ≫ ψ) (j ≫ ψ) ≫ j ≫ ι' →
        ρ' ≫ pullback.snd π' π' = pullback.snd (j ≫ ψ) (j ≫ ψ) ≫ j ≫ ι' →
        ∀ w ∈ closure (pointsMap B S hS _ ρ' ''
            (Set.range (pointsMap B S hS U₁ (pullback.diagonal (j ≫ ψ))))ᶜ),
          pointsMap B S hS (pullback π' π') (pullback.fst π' π') w ∈ R →
          pointsMap B S hS (pullback π' π') (pullback.snd π' π') w ∈ R → False := by
  have : Mono ι := mono_of_presheaf_isOpenImmersion hι
  have hXN : IsNoetherian B S hS hZ X.1 := isNoetherian_of_isProper hZ X.2 Y.2 hYN _ hπ
  have hP : IsAlgebraicSpace B S hS (pullback π.hom π.hom) :=
    isAlgebraicSpace_pullback B S hS π.hom π.hom X.2 X.2 Y.2
  have hιopen : IsOpen (Set.range (pointsMap B S hS V ι)) :=
    isOpen_range_pointsMap_of_isOpenImmersion B S hS _ hι
  let ρ : pullback (j ≫ ψ) (j ≫ ψ) ⟶ pullback π.hom π.hom :=
    pullback.map (j ≫ ψ) (j ≫ ψ) π.hom π.hom (j ≫ ι) (j ≫ ι) q (by simp [h]) (by simp [h])
  let O := pointsMap B S hS _ ρ '' (Set.range (pointsMap B S hS U₁ (pullback.diagonal (j ≫ ψ))))ᶜ
  let T := pointsMap B S hS U₁ (j ≫ ι) '' (pointsMap B S hS U₁ (j ≫ ψ) ⁻¹' Zs)
  let Ob : ClosedSubspaces B S hS (pullback π.hom π.hom) :=
    ⟨reducedClosedSubspace B S hS _ hP (closure O) isClosed_closure,
      isClosedSubspace_reducedClosedSubspace B S hS _ hP _ isClosed_closure⟩
  let D : ClosedSubspaces B S hS X.1 :=
    ⟨reducedClosedSubspace B S hS _ X.2 (closure T) isClosed_closure,
      isClosedSubspace_reducedClosedSubspace B S hS _ X.2 _ isClosed_closure⟩
  let Yb : ClosedSubspaces B S hS X.1 :=
    ⟨reducedClosedSubspace B S hS _ X.2 _ hιopen.isClosed_compl,
      isClosedSubspace_reducedClosedSubspace B S hS _ X.2 _ hιopen.isClosed_compl⟩
  obtain ⟨M, hM⟩ := exists_forall_isBlowupAlong_mem_coincidenceLocus hZ hπ hYN hV hU hU₁ hψ hι
    hj h hf Zs hZs hiso (ρ := ρ) (by simp [ρ]) (by simp [ρ]) Ob
    (range_pointsMap_ι_reducedClosedSubspace B S hS _ hP _ _) D Yb
    (range_pointsMap_ι_reducedClosedSubspace B S hS _ X.2 _ _)
    (range_pointsMap_ι_reducedClosedSubspace B S hS _ X.2 _ _)
  obtain ⟨X', β, hβ⟩ := exists_isBlowupAlong (schemeTheoreticIntersection B S hS X.1 X.2 D
    (infinitesimalNeighbourhood B S hS X Yb M))
  have hZcV : Disjoint (Set.range (pointsMap B S hS V ι)) (subspacePointSet B S hS X.1
      (schemeTheoreticIntersection B S hS X.1 X.2 D
        (infinitesimalNeighbourhood B S hS X Yb M)).1) := by
    rw [Set.disjoint_right]
    intro x hx
    have hx' := subspacePointSet_infinitesimalNeighbourhood_subset X Yb M
      ((subspacePointSet_inf B S hS _ _ ▸ hx).2)
    have hYbpts : subspacePointSet B S hS X.1 Yb.1 = (Set.range (pointsMap B S hS V ι))ᶜ :=
      range_pointsMap_ι_reducedClosedSubspace B S hS _ X.2 _ _
    rw [hYbpts] at hx'
    exact hx'
  obtain ⟨ι', hι'β, hι'open, hpre⟩ := exists_isOpenImmersion_lift_of_isBlowupAlong hV hβ hι hZcV
  have hβadm : IsAdmissibleBlowup B S hS
      ⟨Subfunctor.range ι, isOpenSubspace_subfunctorRange B S hS hV hι⟩ β :=
    ⟨_, isFinitePresentation_ι_of_isNoetherian hZ X hXN _, by rwa [subspacePointSet_range], hβ⟩
  have hπ' : IsProper B S hS (β.hom ≫ π.hom) :=
    isProper_comp B S hS X'.2 X.2 Y.2 _ _ (IsAdmissibleBlowup.isProper B S hS hβadm) hπ
  refine ⟨X', β, ι', _, hβadm, hι'β, hι'open, hpre,
    (isOpen_coincidenceLocus B S hS X' _ _).isClosed_compl,
    closure_image_subset_compl_coincidenceLocus β hι'β Zs D _ (by
      have hDpts : subspacePointSet B S hS X.1 D.1 = closure T :=
        range_pointsMap_ι_reducedClosedSubspace B S hS _ X.2 _ _
      rw [hDpts]; exact subset_closure) hZcV, ?_⟩
  intro π' hπ'eq ρ' hρ'₁ hρ'₂ w hw h₁ h₂
  rcases hM β hβ π' hπ'eq (hπ'eq ▸ hπ') ι' hι'β ρ' hρ'₁ hρ'₂ w hw with hc | hc
  · exact h₁ hc
  · exact h₂ hc

/-- **Separating a closed set from the boundary outside `R`** (step R2 of the repaired proof of
Stacks 0F4B). Let `X` be Noetherian, `ι : V ⟶ X` an open immersion with boundary
`∂ = X ∖ V`, and `C ⊆ R` closed sets of points. Stacks 0F46, part (2), on the open `X ∖ (R ∩ ∂)`
gives a `V`-admissible blowup `b : X' ⟶ X`, through which `ι` lifts, such that the closures of
`b⁻¹(C ∩ V)` and `b⁻¹(∂ ∖ R)` are disjoint. -/
theorem exists_isAdmissibleBlowup_disjoint_closure_boundary (hZ : B.Contains (⊤_ Scheme.{u}))
    {X : AlgebraicSpaces B S hS} (hN : IsNoetherian B S hS hZ X.1)
    {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hV : IsAlgebraicSpace B S hS V) {ι : V ⟶ X.1}
    (hι : IsOpenImmersion B S hS ι) {C R : Set (points B S hS X.1)} (hC : IsClosed C)
    (hR : IsClosed R) (hCR : C ⊆ R) :
    ∃ (X' : AlgebraicSpaces B S hS) (b : X' ⟶ X) (ι' : V ⟶ X'.1),
      IsAdmissibleBlowup B S hS ⟨Subfunctor.range ι, isOpenSubspace_subfunctorRange B S hS hV hι⟩
        b ∧ ι' ≫ b.hom = ι ∧ IsOpenImmersion B S hS ι' ∧
      (∀ A : Set (points B S hS V),
        pointsMap B S hS _ b.hom ⁻¹' (pointsMap B S hS V ι '' A) = pointsMap B S hS V ι' '' A) ∧
      Disjoint (closure (pointsMap B S hS _ b.hom ⁻¹' (C ∩ Set.range (pointsMap B S hS V ι))))
        (closure (pointsMap B S hS _ b.hom ⁻¹' ((Set.range (pointsMap B S hS V ι))ᶜ \ R))) := by
  have : Mono ι := mono_of_presheaf_isOpenImmersion hι
  have hιopen : IsOpen (Set.range (pointsMap B S hS V ι)) :=
    isOpen_range_pointsMap_of_isOpenImmersion B S hS _ hι
  set W := (R ∩ (Set.range (pointsMap B S hS V ι))ᶜ)ᶜ with hWdef
  have hWopen : IsOpen W := (hR.inter hιopen.isClosed_compl).isOpen_compl
  let Uo : OpenSubspaces B S hS X.1 :=
    ⟨openSubspaceOfPoints B S hS X.1 W, isOpenSubspace_openSubspaceOfPoints B S hS X.2 W hWopen⟩
  have hUr : Set.range (pointsMap B S hS _ Uo.1.ι) = W :=
    range_pointsMap_ι_openSubspaceOfPoints B S hS W
  have hVW : Set.range (pointsMap B S hS V ι) ⊆ W := fun x hx hx' => hx'.2 hx
  obtain ⟨X', b, ι', hb, hι'b, hι'open, hpre, hcl⟩ :=
    exists_isAdmissibleBlowup_lift_disjoint_closure hZ hN hV hι Uo (hUr ▸ hVW)
    (hC.preimage (continuous_pointsMap B S hS _))
    (hιopen.isClosed_compl.preimage (continuous_pointsMap B S hS _))
    (by
      rw [Set.disjoint_iff]
      rintro x ⟨hx₁, hx₂⟩
      have hxW : pointsMap B S hS _ Uo.1.ι x ∈ W := hUr ▸ ⟨x, rfl⟩
      exact hxW ⟨hCR hx₁, hx₂⟩)
  refine ⟨X', b, ι', hb, hι'b, hι'open, hpre, ?_⟩
  refine Set.disjoint_of_subset (closure_mono (Set.preimage_mono ?_))
    (closure_mono (Set.preimage_mono ?_)) hcl
  · rintro x ⟨hxC, hxV⟩
    obtain ⟨y, hy⟩ : x ∈ Set.range (pointsMap B S hS _ Uo.1.ι) := hUr ▸ hVW hxV
    exact ⟨y, by rw [Set.mem_preimage, hy]; exact hxC, hy⟩
  · rintro x ⟨hxV, hxR⟩
    obtain ⟨y, hy⟩ : x ∈ Set.range (pointsMap B S hS _ Uo.1.ι) := hUr ▸ fun h => hxR h.1
    exact ⟨y, by rw [Set.mem_preimage, hy]; exact hxV, hy⟩

end Repair

end AlgebraicGeometry.Space

end
