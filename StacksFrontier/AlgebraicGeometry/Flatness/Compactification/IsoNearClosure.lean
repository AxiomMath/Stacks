module

public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleComposition
public import StacksFrontier.AlgebraicGeometry.Blowup.AdmissibleExtension
public import StacksFrontier.AlgebraicGeometry.Blowup.CompositeCentre
public import StacksFrontier.AlgebraicGeometry.Blowup.Separation
import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransformIsoNearClosure
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Flat
public import StacksFrontier.AlgebraicGeometry.Blowup.Transform.Product
public import StacksFrontier.AlgebraicGeometry.Flatness.Compactification.NagataInputs
public import StacksFrontier.AlgebraicGeometry.Flatness.Compactification.StrictTransformOpenSubscheme
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.AlmostBlowUp.IsomorphismAwayFromCenter
public import StacksFrontier.AlgebraicGeometry.Properties.ExtendFiniteType.QuasiCompactOpenIdeal
public import StacksCore.Tactic.StacksAttribute

/-!
# A blowup making a strict transform an isomorphism near a closed set

Let `f : X ⟶ Y` be a proper morphism of quasi-compact and quasi-separated schemes, let `V ⊆ Y`
be a quasi-compact open and let `T ⊆ V` be closed in `V`. If `f` is an isomorphism over some
open between `T` and `V`, then a `V`-admissible blowup of `Y` makes the strict transform of `X`
an isomorphism over an open neighbourhood of the closure of the inverse image of `T`.

## Main results

* `AlgebraicGeometry.exists_isAdmissibleBlowup_strictTransform_isIso_near_closure` constructs
  the blowup and the open neighbourhood.

## Implementation notes

The argument is the one of [Stacks, Tag 0F3W]. First separate `T` from the complement of the
open over which `f` is already an isomorphism: both are closed in `V`, so they sit inside
disjoint closed constructible subsets of `V`, and [Stacks, Tag 0F3V] gives a `V`-admissible
blowup `Y₁ ⟶ Y` in which their closures are disjoint. Over a quasi-compact open `K` of `Y₁`
containing the closure of the inverse image of `T` and missing the closure of the other set,
the base change of `f` is an isomorphism over the inverse image of `V`; so [Stacks, Tag 081T]
dominates it by an admissible blowup of `K`, which [Stacks, Tag 080M] extends to a blowup of
`Y₁`, and [Stacks, Tag 080L] composes the two blowups into a single `V`-admissible blowup of
`Y`. Finally, on the open `W'` lying over `K` the dominating morphism is a section of the base
change, so the strict transform is an isomorphism there.

The last step is the only one needing the strict transform itself. Its defining ideal is the
kernel of the inclusion of the complement of the inverse image of the exceptional divisor
(`AlgebraicGeometry.strictTransform_ideal_eq_ker`), and that complement is the inverse
image of the open complement of the centre, over which the base change has a section; a
scheme-theoretic image of a section whose own kernel ideal vanishes is an isomorphism onto its
target.

## References

* [Stacks Project, Tag 0F3W](https://stacks.math.columbia.edu/tag/0F3W)
* [Stacks Project, Tag 0F3V](https://stacks.math.columbia.edu/tag/0F3V)
* [Stacks Project, Tag 081T](https://stacks.math.columbia.edu/tag/081T)
* [Stacks Project, Tag 080M](https://stacks.math.columbia.edu/tag/080M)
* [Stacks Project, Tag 080L](https://stacks.math.columbia.edu/tag/080L)
* [Stacks Project, Tag 080A](https://stacks.math.columbia.edu/tag/080A)
* [Stacks Project, Tag 080F](https://stacks.math.columbia.edu/tag/080F)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Compactification

/-- Being an isomorphism over an open passes to the restriction of a further restriction, as
soon as the intersection of the two opens lies inside an open over which the morphism is an
isomorphism. -/
private alias isIso_morphismRestrict_restrict_of_inf_le :=
    AlgebraicGeometry.isIso_morphismRestrict_morphismRestrict_of_inf_le

/-- The kernel ideal of an open immersion pulls back along a cartesian square to the kernel
ideal of its base change. -/
private lemma ker_comap_of_isPullback {X Y U V : Scheme.{u}}
    (f : X ⟶ Y) (g : U ⟶ V) (iU : U ⟶ X) (iV : V ⟶ Y)
    [IsOpenImmersion iV] [QuasiCompact f] (h : IsPullback g iU iV f) :
    f.ker.comap iV = g.ker := by
  ext W
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    Scheme.ker_ideal_of_isPullback_of_isOpenImmersion f g iU iV h]

/-- The kernel ideal of the inclusion of a retrocompact open pulls back along an open immersion
to the kernel ideal of the inclusion of the inverse image. -/
private alias ker_ι_comap := AlgebraicGeometry.ker_comap_opens_ι

/-- The complement of the exceptional divisor of a blowup carries no sections of the structure
sheaf supported on the exceptional divisor: its kernel ideal vanishes. This is the case of the
identity in [Stacks, Tag 080F], where the strict transform is the whole base change. -/
private lemma ker_ι_exceptional_compl_eq_bot {S : Scheme.{u}} (I : S.IdealSheafData) :
    (Scheme.Opens.ι (⟨(exceptionalIdeal I).supportᶜ,
      (exceptionalIdeal I).support.isClosed.isOpen_compl⟩ : (blowUp I).Opens)).ker = ⊥ := by
  let p : pullback (𝟙 S) (blowUpToBase I) ⟶ blowUp I := pullback.snd (𝟙 S) (blowUpToBase I)
  have : IsIso p := by
    show IsIso (pullback.snd (𝟙 S) (show blowUp I ⟶ S from blowUpToBase I))
    infer_instance
  let U : (blowUp I).Opens :=
    ⟨(exceptionalIdeal I).supportᶜ, (exceptionalIdeal I).support.isClosed.isOpen_compl⟩
  have hI := strictTransformIdeal_eq_bot_of_flat_at_exceptional (𝟙 S) I
    (fun x _ => (Flat.iff_flat_stalkMap (𝟙 S)).mp inferInstance x)
  have hker : (p ⁻¹ᵁ U).ι.ker = ⊥ := (strictTransform_ideal_eq_ker (𝟙 S) I).symm.trans hI
  show U.ι.ker = ⊥
  calc
    U.ι.ker = ((p ∣_ U) ≫ U.ι).ker := (Scheme.Hom.ker_comp_of_isIso _ _).symm
    _ = ((p ⁻¹ᵁ U).ι ≫ p).ker := by rw [morphismRestrict_ι]
    _ = p.ker := by rw [Scheme.Hom.ker_comp, hker, Scheme.IdealSheafData.map_bot]
    _ = ⊥ := Scheme.Hom.ker_eq_bot_of_isIso p

/-- The inverse image of an open on which a morphism with a section is an isomorphism has the
same kernel ideal as the section, provided the open itself has vanishing kernel ideal. -/
private alias ker_ι_preimage_eq_ker_of_section := AlgebraicGeometry.ker_preimage_eq_ker_of_section

/-- A morphism with a closed-immersion section is an isomorphism when restricted to the closed
subscheme cut out by the kernel ideal of the inverse image of an open with vanishing kernel
ideal over which it is an isomorphism. -/
private alias isIso_subschemeι_comp_of_section := AlgebraicGeometry.isIso_subschemeι_comp_of_section

/-- A morphism which has an isomorphism as a base change along the inclusion of an open is an
isomorphism over that open. -/
private alias isIso_morphismRestrict_of_isPullback :=
    AlgebraicGeometry.isIso_morphismRestrict_of_isPullback

/-- The closed subscheme cut out by the kernel ideal of the inverse image of `U` maps
isomorphically onto an open `V` over which the morphism has a section and is an isomorphism
above `U ⊓ V`. -/
private alias isIso_morphismRestrict_ker_subschemeι_comp_of_section :=
    AlgebraicGeometry.isIso_subschemeι_comp_morphismRestrict_of_section

/-- The strict transform maps isomorphically onto an open `W` of the blowup over which the base
change of `f` admits a section, provided the open `U` cutting out the exceptional divisor's
complement is retrocompact and the base change is an isomorphism above `U ⊓ W`. -/
private lemma isIso_morphismRestrict_strictTransformToBlowUp_of_lift
    {X S : Scheme.{u}} (f : X ⟶ S) [IsSeparated f]
    (I : S.IdealSheafData) (U W : (blowUp I).Opens)
    (hU : (U : Set (blowUp I)) = ((exceptionalIdeal I).support : Set (blowUp I))ᶜ)
    [QuasiCompact U.ι] [QuasiCompact ((pullback.snd f (blowUpToBase I)) ⁻¹ᵁ U).ι]
    (g : W.toScheme ⟶ X) (hg : g ≫ f = W.ι ≫ blowUpToBase I)
    [IsIso (((pullback.snd f (blowUpToBase I)) ∣_ W) ∣_ (W.ι ⁻¹ᵁ U))] :
    IsIso (strictTransformToBlowUp f I ∣_ W) := by
  let p := pullback.snd f (blowUpToBase I)
  let j : W.toScheme ⟶ Stacks.StrictTransform.baseChange f (blowUpToBase I) :=
    pullback.lift g W.ι hg
  have hj : j ≫ p = W.ι := pullback.lift_snd _ _ _
  have hUeq : U = (⟨(exceptionalIdeal I).supportᶜ,
      (exceptionalIdeal I).support.isClosed.isOpen_compl⟩ : (blowUp I).Opens) :=
    SetLike.coe_injective hU
  have hker : U.ι.ker = ⊥ := by rw [hUeq]; exact ker_ι_exceptional_compl_eq_bot I
  have hkerW : (W.ι ⁻¹ᵁ U).ι.ker = ⊥ := by
    rw [← ker_ι_comap W.ι U, hker, Scheme.IdealSheafData.comap_bot]
  have hJ : Stacks.StrictTransform.ideal f (blowUpToBase I) (exceptionalIdeal I) =
      (p ⁻¹ᵁ U).ι.ker := by
    rw [hUeq]
    exact strictTransform_ideal_eq_ker f I
  show IsIso (((Stacks.StrictTransform.ideal f (blowUpToBase I)
    (exceptionalIdeal I)).subschemeι ≫ p) ∣_ W)
  rw [hJ]
  exact isIso_morphismRestrict_ker_subschemeι_comp_of_section p U W j hj hkerW

/-- An admissible blowup of a quasi-compact open `V` of a quasi-compact, quasi-separated scheme
is dominated by the blowup in a finitely presented centre whose support is exactly the
complement of `V`: multiply the given centre by one cutting out the complement of `V` and use
[Stacks, Tag 080A]. -/
private alias exists_centre_support_eq_compl_dominating :=
    AlgebraicGeometry.exists_centre_support_eq_compl_dominating

end Stacks.Compactification

namespace AlgebraicGeometry

open Stacks.Compactification

/-- **Stacks Project, Tag 0F3W.** A proper morphism which is an isomorphism over an open
containing a subset `T` closed in a quasi-compact open `V` becomes, after a `V`-admissible
blowup, a morphism whose strict transform is an isomorphism over an open neighbourhood of the
closure of the inverse image of `T`. -/
@[stacks 0F3W]
theorem exists_isAdmissibleBlowup_strictTransform_isIso_near_closure
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    [CompactSpace X] [QuasiSeparatedSpace X]
    [CompactSpace Y] [QuasiSeparatedSpace Y]
    (V : Y.Opens) (hV : IsCompact (V : Set Y))
    (T : Set Y) (hTV : T ⊆ (V : Set Y))
    (hT : IsClosed (V.ι.base ⁻¹' T))
    (hiso : ∃ W : Y.Opens, W ≤ V ∧ T ⊆ (W : Set Y) ∧ IsIso (f ∣_ W)) :
    ∃ I : Y.IdealSheafData,
      FinitePresentation I.subschemeι ∧
      Disjoint (V : Set Y) (I.support : Set Y) ∧
      ∃ W : (blowUp I).Opens,
        closure ((blowUpToBase I).base ⁻¹' T) ⊆ (W : Set (blowUp I)) ∧
        IsIso (strictTransformToBlowUp f I ∣_ W) := by
  classical
  obtain ⟨W, hWV, hTW, hWiso⟩ := hiso
  have : IsIso (f ∣_ W) := hWiso
  have : CompactSpace V.toScheme := isCompact_iff_compactSpace.mp hV
  have : PrespectralSpace V.toScheme := V.ι.isOpenEmbedding.prespectralSpace
  have : QuasiSeparatedSpace V.toScheme := V.ι.isOpenEmbedding.quasiSeparatedSpace
  obtain ⟨A', B', hAA', hBB', hA'closed, hB'closed, hA'constructible,
      hB'constructible, hdisj'⟩ :=
    exists_disjoint_isClosed_isConstructible_superset
      (V.ι.base ⁻¹' T) ((V.ι.base ⁻¹' (W : Set Y))ᶜ) hT
      (W.2.preimage V.ι.continuous).isClosed_compl
      (Set.disjoint_left.mpr fun x hxA hxB => hxB (hTW hxA))
  obtain ⟨Y₁, b₁, hb₁, hclosures⟩ :=
    exists_isAdmissibleBlowup_disjoint_closures V hV A' B' hA'closed hB'closed
      hA'constructible hB'constructible hdisj'
  have : IsSeparated b₁ := Stacks.Blowup.IsAdmissibleBlowup.isSeparated hb₁
  have : IsIso (b₁ ∣_ V) := isIso_morphismRestrict_of_isAdmissibleBlowup V b₁ hb₁
  have hV₁ : IsCompact ((b₁ ⁻¹ᵁ V : Y₁.Opens) : Set Y₁) :=
    isCompact_preimage_of_isIso_morphismRestrict b₁ V hV
  let Y₀ : Y₁.Opens :=
    ⟨(closure (b₁.base ⁻¹' (V.ι.base '' B')))ᶜ, isClosed_closure.isOpen_compl⟩
  have hTY₀ : closure (b₁.base ⁻¹' T) ⊆ (Y₀ : Set Y₁) := by
    have hTA : T ⊆ V.ι.base '' A' := fun y hy => ⟨⟨y, hTV hy⟩, hAA' hy, rfl⟩
    have hsub := closure_mono (Set.preimage_mono hTA (f := b₁.base))
    exact fun _ hx hy => Set.disjoint_left.mp hclosures (hsub hx) hy
  have hY₀good : (b₁ ⁻¹ᵁ V) ⊓ Y₀ ≤ b₁ ⁻¹ᵁ W := by
    intro x hx
    by_contra hxW
    exact hx.2 (subset_closure ⟨⟨b₁ x, hx.1⟩, hBB' hxW, rfl⟩)
  have : IsProper b₁ := isProper_of_isAdmissibleBlowup V b₁ hb₁
  have : CompactSpace Y₁ := QuasiCompact.compactSpace_of_compactSpace b₁
  have : QuasiSeparatedSpace Y₁ := quasiSeparatedSpace_of_quasiSeparated b₁
  obtain ⟨Kset, hKopen, hKcompact, hTK, hKY₀⟩ :=
    exists_isOpen_isCompact_between
      (show IsCompact (closure (b₁.base ⁻¹' T)) from isClosed_closure.isCompact) Y₀.2 hTY₀
  let K : Y₁.Opens := ⟨Kset, hKopen⟩
  let V₁ := b₁ ⁻¹ᵁ V
  let V₀ := K.ι ⁻¹ᵁ V₁
  have : CompactSpace K.toScheme := isCompact_iff_compactSpace.mp hKcompact
  have : QuasiSeparatedSpace K.toScheme := K.ι.isOpenEmbedding.quasiSeparatedSpace
  have hV₀ : IsCompact (V₀ : Set K.toScheme) := by
    have hKV : IsCompact (Kset ∩ (V₁ : Set Y₁)) :=
      hKcompact.inter_of_isOpen hV₁ hKopen V₁.2
    refine K.ι.isOpenEmbedding.isEmbedding.isCompact_iff.mpr ?_
    convert hKV using 1
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨hxK, hxV⟩
      exact ⟨⟨x, hxK⟩, hxV, rfl⟩
  let f₀ := pullback.snd f (K.ι ≫ b₁)
  have : IsProper f₀ := by dsimp only [f₀]; infer_instance
  have : IsIso (f₀ ∣_ ((K.ι ≫ b₁) ⁻¹ᵁ W)) :=
    isIso_morphismRestrict_pullback_snd_preimage f (K.ι ≫ b₁) W
  have : IsIso (f₀ ∣_ V₀) := by
    refine Stacks.RestrictIso.isIso_morphismRestrict_of_le f₀
      (Ω := (K.ι ≫ b₁) ⁻¹ᵁ W) ?_ inferInstance
    intro x hx
    exact hY₀good ⟨hx, hKY₀ x.2⟩
  have : IsSeparated f₀ := by dsimp only [f₀]; infer_instance
  have : QuasiCompact f₀ := by dsimp only [f₀]; infer_instance
  have : LocallyOfFiniteType f₀ := by dsimp only [f₀]; infer_instance
  obtain ⟨Z₀, c₀, hc₀, g₀, hg₀⟩ :=
    exists_isAdmissibleBlowup_dominating_of_isCompact f₀ V₀ hV₀
      (strictTransformOpenImmersion_of_isIso_morphismRestrict f₀ V₀ hV₀)
  obtain ⟨Y₂, b₂, hb₂, j₀, H⟩ :=
    Stacks.Blowup.exists_admissibleBlowup_isPullback V₁ K hV₁ hKcompact c₀ hc₀
  have hb : Stacks.Blowup.IsAdmissibleBlowup V (b₂ ≫ b₁) :=
    Stacks.Blowup.IsAdmissibleBlowup.comp V b₁ b₂ hb₁ hb₂
  obtain ⟨I, hI, hIV, a, ha⟩ := exists_centre_support_eq_compl_dominating V hV _ hb
  let b : blowUp I ⟶ Y := blowUpToBase I
  let W' := (a ≫ b₂) ⁻¹ᵁ K
  let q : W'.toScheme ⟶ Z₀ := H.lift ((a ≫ b₂) ∣_ K) (W'.ι ≫ a)
    (by rw [morphismRestrict_ι]; exact (Category.assoc _ _ _).symm)
  have hq : q ≫ c₀ = (a ≫ b₂) ∣_ K := H.lift_fst _ _ _
  let g : W'.toScheme ⟶ X := q ≫ g₀ ≫ pullback.fst f (K.ι ≫ b₁)
  have hg : g ≫ f = W'.ι ≫ b := by
    dsimp only [g]
    rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc g₀,
      hg₀, ← Category.assoc q, hq, ← Category.assoc, morphismRestrict_ι, Category.assoc,
      Category.assoc, ha]
  have hdisj : Disjoint (V : Set Y) (I.support : Set Y) := by
    rw [hIV]
    exact disjoint_compl_right
  have hab : (a ≫ b₂) ≫ b₁ = b := by rw [Category.assoc, ha]
  refine ⟨I, hI, hdisj, W', ?_, ?_⟩
  · show closure (b.base ⁻¹' T) ⊆ (W' : Set _)
    rw [← hab]
    exact fun x hx => hTK ((a ≫ b₂).continuous.closure_preimage_subset _ hx)
  · let U := b ⁻¹ᵁ V
    have hU : (U : Set (blowUp I)) = ((exceptionalIdeal I).support : Set (blowUp I))ᶜ := by
      ext x
      show b x ∈ V ↔ x ∉ (I.comap b).support
      rw [Scheme.IdealSheafData.support_comap]
      show b x ∈ V ↔ b x ∉ (I.support : Set Y)
      rw [hIV]
      simp
    have : IsProper b :=
      isProper_blowUpToBase_of_fg I ((finitePresentation_subschemeι_iff_isFiniteType I).mp hI)
    have : QuasiSeparatedSpace (blowUp I) := quasiSeparatedSpace_of_quasiSeparated b
    have : IsIso (b ∣_ V) := isIso_morphismRestrict_of_isAdmissibleBlowup V b
      ((Stacks.Blowup.isAdmissibleBlowup_iff V b).mpr
        ⟨I, hI, hdisj, Iso.refl _, by simp [b]⟩)
    have hUc : IsCompact (U : Set (blowUp I)) :=
      isCompact_preimage_of_isIso_morphismRestrict b V hV
    have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hUc
    have : QuasiCompact U.ι := inferInstance
    let p : Stacks.StrictTransform.baseChange f b ⟶ blowUp I := pullback.snd f b
    have : IsProper p := by dsimp only [p]; infer_instance
    have : QuasiSeparatedSpace (Stacks.StrictTransform.baseChange f b) :=
      quasiSeparatedSpace_of_quasiSeparated p
    have hpc : IsCompact ((p ⁻¹ᵁ U : (Stacks.StrictTransform.baseChange f b).Opens) :
        Set (Stacks.StrictTransform.baseChange f b)) := p.isCompact_preimage hUc
    have : CompactSpace (p ⁻¹ᵁ U).toScheme := isCompact_iff_compactSpace.mp hpc
    have : QuasiCompact (p ⁻¹ᵁ U).ι := inferInstance
    have : IsIso (p ∣_ (b ⁻¹ᵁ W)) := isIso_morphismRestrict_pullback_snd_preimage f b W
    have : IsIso ((p ∣_ W') ∣_ (W'.ι ⁻¹ᵁ U)) := by
      refine isIso_morphismRestrict_restrict_of_inf_le p U W' (b ⁻¹ᵁ W) ?_ inferInstance
      intro x hx
      have hxV : b x ∈ V := hx.2
      rw [← hab] at hxV ⊢
      exact hY₀good ⟨hxV, hKY₀ hx.1⟩
    exact isIso_morphismRestrict_strictTransformToBlowUp_of_lift f I U W' hU g hg

end AlgebraicGeometry

end
