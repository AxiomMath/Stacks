module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TrivialRingSheafModules
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactPlusHomologyCompatible
public import StacksFrontier.AlgebraicGeometry.Blowup.RegularSurfaceBlowupGlobal
public import StacksFrontier.AlgebraicGeometry.Blowup.SmoothCentre
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionFinitePresentation.Basic
public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupFormsKernelEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.Basic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.Composition
public import StacksFrontier.AlgebraicGeometry.PushforwardRegularity.OpenBaseChange

/-!
# Blowing up a smooth centre: the reduction of Stacks 0FUU to the coordinate situation

Let `f : X ⟶ S` be smooth and let `i : Z ⟶ X` be a closed immersion with `Z` smooth over `S`;
write `b : X' ⟶ X` for the blowing up along `Z`, `E` for its exceptional divisor and
`p : E ⟶ Z` for the projection onto the centre. This file carries out the étale-local reduction
of [Stacks, Tag 0FUU] to the coordinate situation `𝐀^m_S ⊆ 𝐀^{m+n}_S` of
[Stacks, Tag 0FUR]: by [Stacks, Tag 0FUE] every point of `Z` has an open neighbourhood `U ⊆ X` on
which the situation is the pullback of the coordinate situation along an étale
`U ⟶ 𝐀^{m+n}_S`, and off the centre the blowing-up morphism is an isomorphism.

## Main results

* `Stacks.DeRham.quasiCompact_blowUpToBase_of_smooth`: the blowing-up morphism of a closed
  immersion of schemes smooth over `S` is quasi-compact; the centre is of finite presentation.
* `Stacks.DeRham.coordinateSubspaceEmbedding_zero`: the coordinate subspace of codimension `0` is
  the whole affine space.
* `Stacks.DeRham.isZero_blowupFormsKernelHigherDirectImage_of_isIso`: where the blowing-up
  morphism is an isomorphism, the higher direct images of the kernel of the restriction of forms
  vanish.

## References

* [Stacks Project, Tag 0FUU](https://stacks.math.columbia.edu/tag/0FUU)
* [Stacks Project, Tag 0FUE](https://stacks.math.columbia.edu/tag/0FUE)
* [Stacks Project, Tag 0FUR](https://stacks.math.columbia.edu/tag/0FUR)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DeRham.BlowupTriangle

universe u

attribute [-instance] CategoryTheory.catToReflQuiver

attribute [local instance] Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding_isClosedImmersion

namespace Stacks.DeRham

/-! ### Quasi-compactness of the blowing-up morphism -/

/-- **The blowing-up morphism of a closed immersion of schemes smooth over `S` is
quasi-compact.** The closed immersion is locally of finite presentation, `Z` being smooth over
`S` and `X` of finite type over `S`, so its ideal sheaf is of finite type and the blowup is
proper. -/
theorem quasiCompact_blowUpToBase_of_smooth {S X Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X)
    [IsClosedImmersion i] [Smooth f] [Smooth (i ≫ f)] :
    QuasiCompact (Stacks.Blowup.blowUpToBase i.ker) := by
  have : LocallyOfFinitePresentation i := locallyOfFinitePresentation_of_comp i f
  exact Stacks.Blowup.quasiCompact_blowUpToBase_of_fg i.ker
    ((locallyOfFinitePresentation_iff_fg_ker i).1 this)

/-- The blowing-up morphism of the coordinate situation `𝐀^m_S ⊆ 𝐀^{m+n}_S` is quasi-compact. -/
theorem quasiCompact_blowUpToBase_coordinateSubspaceEmbedding (S : Scheme.{u}) (m n : ℕ) :
    QuasiCompact (Stacks.Blowup.blowUpToBase
      (Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding S m n).ker) := by
  have := Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding_isClosedImmersion S m n
  have := smooth_affineSpace_over (ULift.{u} (Fin (m + n))) S
  have : Smooth (Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding S m n ≫
      𝔸(ULift.{u} (Fin (m + n)); S) ↘ S) := by
    rw [Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding_over]
    exact smooth_affineSpace_over _ S
  exact quasiCompact_blowUpToBase_of_smooth (𝔸(ULift.{u} (Fin (m + n)); S) ↘ S) _

/-! ### The coordinate subspace of codimension zero -/

/-- **The coordinate subspace of codimension `0` is the whole affine space**: the embedding
`𝐀^m_S ⟶ 𝐀^{m+0}_S` is the identity. -/
theorem coordinateSubspaceEmbedding_zero (S : Scheme.{u}) (m : ℕ) :
    Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding S m 0 = 𝟙 _ := by
  refine AffineSpace.hom_ext ?_ ?_
  · rw [Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding_over, Category.id_comp]
    rfl
  · rintro ⟨j⟩
    have h := Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding_firstCoordinate S m 0 j
    rw [show Fin.castAdd 0 j = j from Fin.ext rfl] at h
    rw [h]
    rfl

/-! ### Off the centre -/

/-- The right derived functors of the direct image along an isomorphism of schemes vanish in
nonzero degrees: the direct image is then an equivalence, hence exact. -/
theorem isZero_rightDerivedPlus_pushforward_of_isIso {Y Y' : Scheme.{u}} (g : Y' ⟶ Y) [IsIso g]
    [HasDerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing Y'.toRingedSpace))]
    [HasDerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))]
    [EnoughInjectives (_root_.SheafOfModules.{u} (structureSheafRing Y'.toRingedSpace))]
    (F : _root_.SheafOfModules.{u} (structureSheafRing Y'.toRingedSpace)) (q : ℤ) (hq : q ≠ 0) :
    IsZero (((modulePushforward g.toLRSHom.toShHom).rightDerivedPlus q).obj F) := by
  have hpl : PreservesFiniteLimits (modulePushforward g.toLRSHom.toShHom) := by
    have : PreservesLimitsOfSize.{0, 0} (modulePushforward g.toLRSHom.toShHom) :=
      (modulePullbackPushforwardAdjunction g.toLRSHom.toShHom).rightAdjoint_preservesLimits
    infer_instance
  have hpc : PreservesFiniteColimits (modulePushforward g.toLRSHom.toShHom) :=
    inferInstanceAs (PreservesFiniteColimits
      (Stacks.AlgebraicGeometry.OpenBaseChange.pushforwardEquivalence (asIso g)).functor)
  have hz : IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F)) := by
    rcases lt_or_gt_of_ne hq with h | h
    · exact DerivedCategory.Plus.isZero_homology_of_isGE _ 0 q h
    · exact DerivedCategory.Plus.isZero_homology_of_isLE _ 0 q h
  exact ((modulePushforward g.toLRSHom.toShHom).map_isZero hz).of_iso
    ((Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso
      (modulePushforward g.toLRSHom.toShHom) q).app _)

/-- **Where the blowing-up morphism is an isomorphism, `R^q b_*𝒦^a = 0` for `q ≠ 0`.** -/
theorem isZero_blowupFormsKernelHigherDirectImage_of_isIso {S X Z : Scheme.{u}} (f : X ⟶ S)
    (i : Z ⟶ X) [IsClosedImmersion i] [IsIso (Stacks.Blowup.blowUpToBase i.ker)] (a q : ℤ)
    (hq : q ≠ 0) : IsZero (blowupFormsKernelHigherDirectImage f i a q) :=
  @isZero_rightDerivedPlus_pushforward_of_isIso _ _ (blowupMap i) _
    (HasDerivedCategory.standard _) (HasDerivedCategory.standard _) _ _ q hq

/-! ### The covering argument -/

/-- Opens containing a point each, indexed by the points, cover the space. -/
private theorem iSup_eq_top_of_forall_mem {T : Type*} [TopologicalSpace T]
    (U : T → TopologicalSpace.Opens T) (h : ∀ x, x ∈ U x) : ⨆ x, U x = ⊤ :=
  top_le_iff.1 fun x _ => TopologicalSpace.Opens.mem_iSup.2 ⟨x, h x⟩

section Covering

variable {S X Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X) [IsClosedImmersion i] [Smooth f]
  [Smooth (i ≫ f)]

/-- Every point of the centre has a chart of [Stacks, Tag 0FUE]: an étale `π` to the coordinate
situation, whose pullback is the centre, with quasi-compact blowing-up morphism. -/
private theorem exists_etale_chart_of_mem_centre {P : Prop} (z : Z)
    (h : ∀ (m n : ℕ) (U : X.Opens), z ∈ i ⁻¹ᵁ U →
      ∀ (π : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin (m + n))) S)
        (q : (i ⁻¹ᵁ U).toScheme ⟶ AffineSpace (ULift.{u} (Fin m)) S) [Etale π]
        [QuasiCompact (Stacks.Blowup.blowUpToBase
          (Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding S m n).ker)],
        π ≫ (AffineSpace.over (ULift.{u} (Fin (m + n))) S).hom = (U.ι ≫ f) ≫ 𝟙 S →
        IsPullback (restrictCentre i U) q π
          (Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding S m n) → P) : P := by
  obtain ⟨m, n, U, hzU, π, q, hπ, hbase, hpb⟩ :=
    Stacks.AlgebraicGeometry.exists_etale_coordinateSubspaceEmbedding_isPullback f i z
  have := hπ
  have := quasiCompact_blowUpToBase_coordinateSubspaceEmbedding S m n
  exact h m n U hzU π q (hbase.trans (Category.comp_id _).symm) hpb

/-- **A centre with empty interior has positive codimension in every chart.** If no nonempty open
subset of `X` is contained in `Z`, then the coordinate charts of [Stacks, Tag 0FUE] around the
points of `Z` have `n ≥ 1`: for `n = 0` the coordinate subspace is everything, so the chart would
be an open of `X` contained in `Z`. -/
theorem one_le_of_interior_range_eq_empty (hint : interior (Set.range i.base) = ∅) {m n : ℕ}
    {U : X.Opens} {z : Z} (hz : z ∈ i ⁻¹ᵁ U)
    {π : U.toScheme ⟶ AffineSpace (ULift.{u} (Fin (m + n))) S}
    {q : (i ⁻¹ᵁ U).toScheme ⟶ AffineSpace (ULift.{u} (Fin m)) S}
    (hpb : IsPullback (restrictCentre i U) q π
      (Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding S m n)) : 1 ≤ n := by
  by_contra hn
  obtain rfl : n = 0 := by omega
  have : IsIso (Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding S m 0) := by
    rw [coordinateSubspaceEmbedding_zero]
    infer_instance
  have hiso : IsIso (restrictCentre i U) := hpb.isIso_fst_of_isIso
  have hsub : (U : Set X) ⊆ Set.range i.base := by
    intro x hx
    obtain ⟨y, hy⟩ := (restrictCentre i U).surjective ⟨x, hx⟩
    have h : (restrictCentre i U ≫ U.ι) y = ((i ⁻¹ᵁ U).ι ≫ i) y := by
      rw [Scheme.Hom.resLE_comp_ι]
    rw [Scheme.Hom.comp_apply, Scheme.Hom.comp_apply, hy] at h
    simp only [Scheme.Opens.ι_apply] at h
    exact ⟨y.1, h.symm⟩
  have hU := interior_maximal hsub U.isOpen
  rw [hint] at hU
  exact hU hz

/-- The complement of the centre, on which the blowing-up morphism is an isomorphism. -/
abbrev centreComplement : X.Opens :=
  ⟨(Set.range i.base)ᶜ, i.isClosedEmbedding.isClosed_range.isOpen_compl⟩

omit [Smooth f] [Smooth (i ≫ f)] in
/-- Over the complement of the centre the blowing-up morphism is an isomorphism. -/
theorem isIso_blowUpToBase_restrictCentre_centreComplement :
    IsIso (Stacks.Blowup.blowUpToBase (restrictCentre i (centreComplement i)).ker) := by
  have hempty : IsEmpty ↥(i ⁻¹ᵁ centreComplement i) := by
    refine ⟨fun y => ?_⟩
    have hy : i.base y.1 ∈ centreComplement i := y.2
    exact hy ⟨y.1, rfl⟩
  have hIE : IsEmpty ↥(i ⁻¹ᵁ centreComplement i).toScheme := hempty
  exact isIso_blowUpToBase_of_ker_eq_top (restrictCentre i (centreComplement i))
    (AlgebraicGeometry.Scheme.ker_eq_top_of_isEmpty _)

/-- **Clause (1) of [Stacks, Tag 0FUU] from the coordinate situation.** If the comparison map
`Ω^a_{X/S} ⟶ b_*Ω^a_{X'/S}` is an isomorphism in the coordinate situation `𝐀^m_S ⊆ 𝐀^{m+n}_S`
for every `m` and every `n ≥ 1`, then it is an isomorphism for every closed immersion of schemes
smooth over `S` whose image has empty interior. -/
theorem isIso_blowupFormsDirectImage_of_coordinate
    (hint : interior (Set.range i.base) = ∅) (a : ℕ)
    (hmodel : ∀ m n : ℕ, 1 ≤ n → IsIso (blowupFormsDirectImage
      (Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding S m n)
      (AffineSpace.over (ULift.{u} (Fin (m + n))) S).hom (a : ℤ))) :
    IsIso (blowupFormsDirectImage i f (a : ℤ)) := by
  classical
  have := quasiCompact_blowUpToBase_of_smooth f i
  have hcov : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      IsIso ((Scheme.Modules.pullback U.ι).map (blowupFormsDirectImage i f (a : ℤ))) := by
    intro x
    by_cases hx : x ∈ Set.range i.base
    · obtain ⟨z, rfl⟩ := hx
      refine exists_etale_chart_of_mem_centre f i z fun m n U hzU π q _ _ hbase hpb => ?_
      have hU := isIso_blowupFormsDirectImage_of_isPullback _ (U.ι ≫ f) hpb.flip (𝟙 S) hbase a
        (hmodel m n (one_le_of_interior_range_eq_empty i hint hzU hpb))
      exact ⟨U, hzU, isIso_pullback_map_blowupFormsDirectImage_of_isPullback f (U.ι ≫ f)
        (isPullback_restrictCentre i U) (𝟙 S) (Category.comp_id _).symm a hU⟩
    · have := isIso_blowUpToBase_restrictCentre_centreComplement i
      exact ⟨centreComplement i, hx,
        isIso_pullback_map_blowupFormsDirectImage_of_isPullback f (_ ≫ f)
          (isPullback_restrictCentre i _) (𝟙 S) (Category.comp_id _).symm a
          (isIso_blowupFormsDirectImage_of_isIso_blowUpToBase _ _ _)⟩
  choose U hxU hU using hcov
  refine Scheme.Modules.isIso_of_isIso_pullback_ι U ?_ _ hU
  exact iSup_eq_top_of_forall_mem U hxU

/-- **Clause (2) of [Stacks, Tag 0FUU] from the coordinate situation.** If the comparison map
`Ω^a_{Z/S} ⟶ p_*Ω^a_{E/S}` is an isomorphism in the coordinate situation `𝐀^m_S ⊆ 𝐀^{m+n}_S`
for every `m` and every `n ≥ 1`, then it is an isomorphism for every closed immersion of schemes
smooth over `S` whose image has empty interior. -/
theorem isIso_exceptionalFormsDirectImage_of_coordinate
    (hint : interior (Set.range i.base) = ∅) (a : ℕ)
    (hmodel : ∀ m n : ℕ, 1 ≤ n → IsIso (exceptionalFormsDirectImage
      (Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding S m n)
      (AffineSpace.over (ULift.{u} (Fin (m + n))) S).hom (a : ℤ))) :
    IsIso (exceptionalFormsDirectImage i f (a : ℤ)) := by
  classical
  have := quasiCompact_blowUpToBase_of_smooth f i
  have hcov : ∀ z : Z, ∃ V : Z.Opens, z ∈ V ∧
      IsIso ((Scheme.Modules.pullback V.ι).map (exceptionalFormsDirectImage i f (a : ℤ))) := by
    intro z
    refine exists_etale_chart_of_mem_centre f i z fun m n U hzU π q _ _ hbase hpb => ?_
    have hU := isIso_exceptionalFormsDirectImage_of_isPullback _ (U.ι ≫ f) hpb.flip (𝟙 S) hbase a
      (hmodel m n (one_le_of_interior_range_eq_empty i hint hzU hpb))
    exact ⟨i ⁻¹ᵁ U, hzU, isIso_pullback_map_exceptionalFormsDirectImage_of_isPullback f (U.ι ≫ f)
      (isPullback_restrictCentre i U) (𝟙 S) (Category.comp_id _).symm a hU⟩
  choose V hzV hV using hcov
  refine Scheme.Modules.isIso_of_isIso_pullback_ι V ?_ _ hV
  exact iSup_eq_top_of_forall_mem V hzV

/-- **The vanishing form of clause (3) of [Stacks, Tag 0FUU] from the coordinate situation.** If
`R^q b_*𝒦^a = 0` in the coordinate situation `𝐀^m_S ⊆ 𝐀^{m+n}_S` for every `m` and `n`, then
`R^q b_*𝒦^a = 0` for every closed immersion of schemes smooth over `S`. -/
theorem isZero_blowupFormsKernelHigherDirectImage_of_coordinate (a : ℕ) (q : ℤ) (hq : q ≠ 0)
    (hmodel : ∀ m n : ℕ, IsZero (blowupFormsKernelHigherDirectImage
      (AffineSpace.over (ULift.{u} (Fin (m + n))) S).hom
      (Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding S m n) (a : ℤ) q)) :
    IsZero (blowupFormsKernelHigherDirectImage f i (a : ℤ) q) := by
  classical
  have := quasiCompact_blowUpToBase_of_smooth f i
  have hcov : ∀ x : X, ∃ U : X.Opens, x ∈ U ∧
      IsZero ((Scheme.Modules.pullback U.ι).obj
        (blowupFormsKernelHigherDirectImage f i (a : ℤ) q)) := by
    intro x
    by_cases hx : x ∈ Set.range i.base
    · obtain ⟨z, rfl⟩ := hx
      refine exists_etale_chart_of_mem_centre f i z fun m n U hzU π q' _ _ hbase hpb => ?_
      have hU := isZero_blowupFormsKernelHigherDirectImage_of_isPullback (U.ι ≫ f) hpb.flip
        (𝟙 S) hbase a q (hmodel m n)
      exact ⟨U, hzU, isZero_pullback_blowupFormsKernelHigherDirectImage_of_isPullback (U.ι ≫ f)
        (isPullback_restrictCentre i U) (𝟙 S) (Category.comp_id _).symm a q hU⟩
    · have := isIso_blowUpToBase_restrictCentre_centreComplement i
      exact ⟨centreComplement i, hx,
        isZero_pullback_blowupFormsKernelHigherDirectImage_of_isPullback (_ ≫ f)
          (isPullback_restrictCentre i _) (𝟙 S) (Category.comp_id _).symm a q
          (isZero_blowupFormsKernelHigherDirectImage_of_isIso _ _ _ q hq)⟩
  choose U hxU hU using hcov
  exact isZero_of_isZero_pullback_ι U
    (iSup_eq_top_of_forall_mem U hxU) hU

end Covering

/-! ### The coordinate situation in codimension zero -/

/-- A sheaf of modules on an empty scheme is zero. -/
theorem isZero_of_isEmpty {Y : Scheme.{u}} [IsEmpty Y] (M : Y.Modules) : IsZero M :=
  isZero_of_isZero_pullback_ι (Y := Y) (fun e : PEmpty.{1} => e.elim)
    (Subsingleton.elim _ _) fun e => e.elim

/-- The right derived functors of a direct image out of an empty scheme vanish in nonzero
degrees: every module on the empty scheme is zero, hence injective. -/
theorem isZero_rightDerivedPlus_pushforward_of_isEmpty {Y Y' : Scheme.{u}} (g : Y' ⟶ Y)
    [IsEmpty Y']
    [HasDerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing Y'.toRingedSpace))]
    [HasDerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing Y.toRingedSpace))]
    [EnoughInjectives (_root_.SheafOfModules.{u} (structureSheafRing Y'.toRingedSpace))]
    (F : _root_.SheafOfModules.{u} (structureSheafRing Y'.toRingedSpace)) (q : ℤ) (hq : q ≠ 0) :
    IsZero (((modulePushforward g.toLRSHom.toShHom).rightDerivedPlus q).obj F) := by
  have hF : IsZero F := Stacks.SheafOfModules.isZero_of_subsingleton_sections
    (fun V => inferInstanceAs (Subsingleton Γ(Y', V))) F
  have : Injective F := Injective.of_iso hF.isoZero.symm inferInstance
  exact Functor.isZero_rightDerivedPlus_obj_injective _ q hq F

/-- **In codimension `0` the blowup of the coordinate situation is empty**: the coordinate
subspace is the whole affine space, its ideal is zero, and the blowup in the zero ideal is
empty. -/
theorem isEmpty_blowUp_coordinateSubspaceEmbedding_zero (S : Scheme.{u}) (m : ℕ) :
    IsEmpty (Stacks.Blowup.blowUp
      (Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding S m 0).ker) := by
  have hker : (Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding S m 0).ker = ⊥ := by
    rw [coordinateSubspaceEmbedding_zero]
    exact Scheme.Hom.ker_eq_bot_of_isIso _
  rw [hker]
  have := AlgebraicGeometry.isEmpty_blowUp_bot (AffineSpace (ULift.{u} (Fin (m + 0))) S)
  exact Function.isEmpty (AlgebraicGeometry.blowUpIso ⊥).inv

/-- **In codimension `0`, `R^q b_*𝒦^a = 0` in the coordinate situation**, for every `q ≠ 0`: the
blowup is empty. -/
theorem isZero_blowupFormsKernelHigherDirectImage_coordinate_zero (S : Scheme.{u}) (m : ℕ)
    (a q : ℤ) (hq : q ≠ 0) :
    IsZero (blowupFormsKernelHigherDirectImage
      (AffineSpace.over (ULift.{u} (Fin (m + 0))) S).hom
      (Stacks.AlgebraicGeometry.coordinateSubspaceEmbedding S m 0) a q) := by
  have := isEmpty_blowUp_coordinateSubspaceEmbedding_zero S m
  exact @isZero_rightDerivedPlus_pushforward_of_isEmpty.{u} _ _ (blowupMap _) _
    (HasDerivedCategory.standard _) (HasDerivedCategory.standard _) _ _ q hq

end Stacks.DeRham

end
