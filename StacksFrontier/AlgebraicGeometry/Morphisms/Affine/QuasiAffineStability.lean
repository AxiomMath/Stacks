module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Constructors
public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.QuasiAffine
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Quasi-affineness of a morphism is affine-local on the target

Quasi-affineness of a morphism of schemes is determined by its restrictions over the affine
opens of the target, and over an affine target it says exactly that the source is a
quasi-affine scheme. This file records that affine-local description and derives from it the
two permanence properties of the class: stability under composition and under arbitrary base
change.

## Main results

* `AlgebraicGeometry.hasAffineProperty_isQuasiAffineHom`: quasi-affineness of a morphism is the
  affine-local property that the source is a quasi-affine scheme.
* `AlgebraicGeometry.isQuasiAffineHom_iff_of_iSup_eq_top`: a morphism is quasi-affine as soon as
  the preimages of the members of one affine open covering of the target are quasi-affine.
* `AlgebraicGeometry.Scheme.IsQuasiAffine.of_isQuasiAffineHom`: the source of a quasi-affine
  morphism into a quasi-affine scheme is quasi-affine.
* `AlgebraicGeometry.isQuasiAffineHom_isStableUnderComposition`: a composition of quasi-affine
  morphisms is quasi-affine.
* `AlgebraicGeometry.isQuasiAffineHom_isStableUnderBaseChange`: an arbitrary base change of a
  quasi-affine morphism is quasi-affine.

## Implementation notes

The affine-local description is phrased with Mathlib's `HasAffineProperty`, whose locality
axioms are formulated over an affine target and for coverings by the basic opens of a family of
global sections spanning the unit ideal. Base change is then supplied by the general theory:
over an affine base with affine source the base change of a morphism is affine, so the base
change of a quasi-affine scheme along it stays quasi-affine by
`AlgebraicGeometry.Scheme.IsQuasiAffine.of_isAffineHom`.

The locality axiom for a covering is the quasi-affine analogue of
`AlgebraicGeometry.isAffine_of_isAffineOpen_basicOpen`: a quasi-compact scheme covered by
quasi-affine basic opens of global sections is quasi-affine. Its proof is the one Mathlib gives
for `AlgebraicGeometry.Scheme.IsQuasiAffine.of_forall_exists_mem_basicOpen`, with "affine"
weakened to "quasi-affine" on the members of the covering: what the proof uses of a member is
that the canonical morphism to the spectrum of its global sections is an open immersion, and
that holds for a quasi-affine scheme too.

Every consequence drawn from `HasAffineProperty` passes that instance explicitly rather than
through typeclass search, because instances whose carried morphism property is a bound variable
are not matched against a concrete property under the current default transparency settings;
Mathlib's own files disable the `backward.isDefEq.respectTransparency.types` check at each such
call site. The facts downstream consumers need are therefore restated here as instances of
their own, whose morphism property is the concrete `IsQuasiAffineHom`.

## References

* [Stacks Project, Tag 01SM](https://stacks.math.columbia.edu/tag/01SM)
* [Stacks Project, Tag 01SN](https://stacks.math.columbia.edu/tag/01SN)
* [Stacks Project, Tag 01SO](https://stacks.math.columbia.edu/tag/01SO)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The basic open subscheme defined by a global section of a quasi-affine scheme is
quasi-affine, being a quasi-compact open subscheme of it. -/
lemma Scheme.isQuasiAffine_basicOpen (X : Scheme.{u}) [X.IsQuasiAffine] (r : Γ(X, ⊤)) :
    (X.basicOpen r).toScheme.IsQuasiAffine := by
  have hc : IsCompact (X.basicOpen r : Set X) := by
    simpa using isRetrocompact_basicOpen (X := X) r isCompact_univ isOpen_univ
  have : CompactSpace (X.basicOpen r).toScheme := isCompact_iff_compactSpace.mp hc
  exact Scheme.IsQuasiAffine.of_isImmersion (X.basicOpen r).ι

/-- A quasi-compact scheme each of whose points lies in a quasi-affine basic open subscheme
defined by a global section is quasi-affine. -/
lemma Scheme.IsQuasiAffine.of_forall_exists_isQuasiAffine_basicOpen (X : Scheme.{u})
    [CompactSpace X]
    (H : ∀ x : X, ∃ r : Γ(X, ⊤), (X.basicOpen r).toScheme.IsQuasiAffine ∧ x ∈ X.basicOpen r) :
    X.IsQuasiAffine := by
  choose r hr hxr using H
  have hcov : ⨆ x, X.basicOpen (r x) = ⊤ :=
    eq_top_iff.mpr fun x _ ↦ Opens.mem_iSup.mpr ⟨x, hxr x⟩
  have hqs : QuasiSeparatedSpace X := by
    refine QuasiSeparatedSpace.of_isOpenCover (U := (X.basicOpen <| r ·)) hcov
      (fun _ ↦ isRetrocompact_basicOpen _) (fun x ↦ ?_)
    have := hr x
    exact (isQuasiSeparated_iff_quasiSeparatedSpace _ (X.basicOpen (r x)).2).mpr
      (inferInstanceAs (QuasiSeparatedSpace (X.basicOpen (r x)).toScheme))
  suffices IsOpenImmersion X.toSpecΓ by constructor
  refine IsZariskiLocalAtTarget.of_forall_source_exists_preimage _ fun x ↦ ?_
  refine ⟨PrimeSpectrum.basicOpen (r x),
    (Scheme.toSpecΓ_preimage_basicOpen X (r x)).ge (hxr x), ?_⟩
  suffices IsOpenImmersion ((X.basicOpen (r x)).ι ≫ X.toSpecΓ) by
    convert! this <;> rw [Scheme.toSpecΓ_preimage_basicOpen]
  rw [← Scheme.Opens.toSpecΓ_SpecMap_presheaf_map_top]
  have := isLocalization_basicOpen_of_qcqs (X := X) isCompact_univ isQuasiSeparated_univ (r x)
  have := hr x
  refine MorphismProperty.comp_mem _ _ _ ?_ (.of_isLocalization (r x))
  change IsOpenImmersion ((X.basicOpen (r x)).toScheme.toSpecΓ ≫
    Spec.map (X.basicOpen (r x)).topIso.inv)
  infer_instance

/-- A scheme covered by the quasi-affine basic open subschemes of a family of global sections
spanning the unit ideal is quasi-affine. -/
lemma Scheme.IsQuasiAffine.of_span_eq_top (X : Scheme.{u}) (s : Set Γ(X, ⊤))
    (hs : Ideal.span s = ⊤) (hs₂ : ∀ i ∈ s, (X.basicOpen i).toScheme.IsQuasiAffine) :
    X.IsQuasiAffine := by
  have : CompactSpace X := by
    obtain ⟨s', hs', e⟩ := (Ideal.span_eq_top_iff_finite _).mp hs
    rw [← isCompact_univ_iff, ← Opens.coe_top, ← iSup_basicOpen_of_span_eq_top _ _ e]
    simp only [Finset.mem_coe, Opens.iSup_mk, Opens.carrier_eq_coe, Opens.coe_mk]
    apply s'.isCompact_biUnion
    exact fun i hi ↦ isCompact_iff_compactSpace.mpr (hs₂ _ (hs' hi)).toCompactSpace
  refine Scheme.IsQuasiAffine.of_forall_exists_isQuasiAffine_basicOpen X fun x ↦ ?_
  have hx : x ∈ (⨆ i ∈ s, X.basicOpen i) := by
    rw [iSup_basicOpen_of_span_eq_top (⊤ : X.Opens) s hs]; trivial
  simp only [Opens.mem_iSup] at hx
  obtain ⟨i, hi, hxi⟩ := hx
  exact ⟨i, hs₂ i hi, hxi⟩

/-- Quasi-affineness of a morphism of schemes is the affine-local property that the source is a
quasi-affine scheme. -/
@[ega "II 5.1.1"]
instance hasAffineProperty_isQuasiAffineHom :
    HasAffineProperty @IsQuasiAffineHom fun X _ _ _ ↦ X.IsQuasiAffine where
  isLocal_affineProperty := by
    constructor
    · apply AffineTargetMorphismProperty.respectsIso_mk
      · rintro X Y Z e _ _ H
        have : Y.IsQuasiAffine := H
        exact Scheme.IsQuasiAffine.of_isAffineHom e.hom
      · exact fun _ _ _ ↦ id
    · intro X Y _ f r H
      have : X.IsQuasiAffine := H
      change Scheme.IsQuasiAffine _
      rw [Scheme.preimage_basicOpen_top]
      exact X.isQuasiAffine_basicOpen _
    · intro X Y _ f S hS hS'
      apply_fun Ideal.map (f.appTop).hom at hS
      rw [Ideal.map_span, Ideal.map_top] at hS
      apply Scheme.IsQuasiAffine.of_span_eq_top _ _ hS
      have : ∀ i : S, Scheme.IsQuasiAffine (f ⁻¹ᵁ Y.basicOpen i.1) := hS'
      simpa [Scheme.preimage_basicOpen] using! this
  eq_targetAffineLocally' := by
    ext X Y f
    simp only [targetAffineLocally, Scheme.affineOpens, Set.coe_ofPred, Set.mem_ofPred_eq,
      Subtype.forall, isQuasiAffineHom_iff]

/-- Quasi-affineness of a morphism of schemes is Zariski-local on the target. -/
instance isZariskiLocalAtTarget_isQuasiAffineHom :
    IsZariskiLocalAtTarget (@IsQuasiAffineHom : MorphismProperty Scheme.{u}) :=
  @HasAffineProperty.instIsZariskiLocalAtTarget _ _ hasAffineProperty_isQuasiAffineHom

/-- **Stacks Project, Tag 01SM, (1) is equivalent to (2).** A morphism of schemes is
quasi-affine if and only if the preimages of the members of one affine open covering of the
target are quasi-affine schemes. -/
@[stacks 01SM "(1) iff (2)"]
theorem isQuasiAffineHom_iff_of_iSup_eq_top {X S : Scheme.{u}} (f : X ⟶ S) {ι : Type*}
    (U : ι → S.Opens) (hU : ∀ i, IsAffineOpen (U i)) (hU' : ⨆ i, U i = ⊤) :
    IsQuasiAffineHom f ↔ ∀ i, (f ⁻¹ᵁ U i).toScheme.IsQuasiAffine :=
  @HasAffineProperty.iff_of_iSup_eq_top @IsQuasiAffineHom _ hasAffineProperty_isQuasiAffineHom
    X S f ι (fun i ↦ ⟨U i, hU i⟩) hU'

/-- The source of a quasi-affine morphism into a quasi-affine scheme is quasi-affine. This
generalizes `AlgebraicGeometry.Scheme.IsQuasiAffine.of_isAffineHom`. -/
lemma Scheme.IsQuasiAffine.of_isQuasiAffineHom {X S : Scheme.{u}} (f : X ⟶ S)
    [IsQuasiAffineHom f] [S.IsQuasiAffine] : X.IsQuasiAffine := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  refine Scheme.IsQuasiAffine.of_forall_exists_isQuasiAffine_basicOpen X fun x ↦ ?_
  obtain ⟨_, ⟨_, ⟨t, ht, rfl⟩, rfl⟩, hxt, -⟩ := (Scheme.IsQuasiAffine.isBasis_basicOpen
    S).exists_subset_of_mem_open (Set.mem_univ (f.base x)) isOpen_univ
  refine ⟨f.appTop t, ?_, ?_⟩
  · rw [← Scheme.preimage_basicOpen_top]
    exact IsQuasiAffineHom.isQuasiAffine_preimage _ ht
  · rw [← Scheme.preimage_basicOpen_top]
    exact hxt

/-- **Stacks Project, Tag 01SN.** A composition of quasi-affine morphisms of schemes is
quasi-affine. -/
@[stacks 01SN, ega "II 5.1.10"]
instance isQuasiAffineHom_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition
      (@IsQuasiAffineHom : MorphismProperty Scheme.{u}) where
  comp_mem {X Y Z} f g hf hg := by
    rw [isQuasiAffineHom_iff_of_iSup_eq_top (f ≫ g) (fun i : Z.affineOpens ↦ (i : Z.Opens))
      (fun i ↦ i.2) (iSup_affineOpens_eq_top Z)]
    intro W
    have hW : (g ⁻¹ᵁ (W : Z.Opens)).toScheme.IsQuasiAffine := hg.isQuasiAffine_preimage _ W.2
    have hres : IsQuasiAffineHom (f ∣_ (g ⁻¹ᵁ (W : Z.Opens))) :=
      IsZariskiLocalAtTarget.restrict hf _
    rw [Scheme.Hom.comp_preimage]
    exact Scheme.IsQuasiAffine.of_isQuasiAffineHom (f ∣_ (g ⁻¹ᵁ (W : Z.Opens)))

/-- **Stacks Project, Tag 01SO.** Quasi-affine morphisms of schemes are stable under arbitrary
base change. -/
@[stacks 01SO, ega "IV 2.7.1" "(xiv)"]
instance isQuasiAffineHom_isStableUnderBaseChange :
    MorphismProperty.IsStableUnderBaseChange
      (@IsQuasiAffineHom : MorphismProperty Scheme.{u}) :=
  @HasAffineProperty.isStableUnderBaseChange _ _ hasAffineProperty_isQuasiAffineHom <| by
    intro Z X Y S _ _ f g f' g' sq hg
    have : Y.IsQuasiAffine := hg
    have : IsAffineHom f' :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback sq inferInstance
    exact Scheme.IsQuasiAffine.of_isAffineHom f'

end AlgebraicGeometry

end
